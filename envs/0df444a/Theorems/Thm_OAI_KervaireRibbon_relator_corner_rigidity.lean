-- Prove2me | Theorems.Thm_OAI_KervaireRibbon_relator_corner_rigidity
-- name    : OAI.KervaireRibbon.relator_corner_rigidity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:56:58.773987+00:00
-- url     : https://prove2.me/theorems/7ceb3fe5-19ba-441f-852c-e5687f034fa7
-- title:
--   Corner rigidity for planar diagrams of relator copies
-- statement:
--   Let $A$ be a group, $I$ a nonempty finite set with a cyclic permutation $\rho$, $a:I\to A$, and $s:I\to\{1,-1\}$ with $\sum_is_i=\pm1$. Let $e:V\times I\to D$ identify the darts of a finite diagram with copies of the relator, with polarities $\varepsilon_v=\pm1$. Let $\sigma,\theta$ be permutations of $D$ such that:
--
--   - $\sigma$ moves $e(v,i)$ to $e(v,\rho i)$ if $\varepsilon_v=1$ and to $e(v,\rho^{-1}i)$ otherwise;
--   - $\theta$ is an involution, and $t:D\to\mathbb Z$ satisfies $t(\theta d)=-t(d)$ and $t(e(v,i))=\varepsilon_vs_i$;
--   - $(\sigma,\theta)$ is connected and planar.
--
--   Let $\mathrm{vc}(v,i)$ be $a_i$ if $\varepsilon_v=1$ and $a_{\rho^{-1}i}^{-1}$ otherwise. Let $u:D\to A$, with $\mathrm{corner}(d)=u(\theta d)\,u(\sigma d)^{-1}$. If $\mathrm{corner}(e(v,i))=\mathrm{vc}(v,i)$ at every dart except $p$, then
--   $$
--   \mathrm{corner}(p)=\mathrm{vc}(e^{-1}p).
--   $$
--
--   This is the rigidity used at relator corners when capping a ribbon diagram.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/RelatorRigidity.lean#L267-L344

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal
import Definitions.Def_OAI_GroupTheory_Kervaire_BoundaryFlow
import Definitions.Def_OAI_GroupTheory_Kervaire_RelatorRigidity

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

theorem OAI.KervaireRibbon.relator_corner_rigidity [Nonempty I]
    (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (e : V × I ≃ D) (ε : V → ℤ) (hε : ∀ v, ε v = 1 ∨ ε v = -1)
    (σ θ : Perm D) (hσ : ∀ v i, σ (e (v,i)) = e (vertexNext ρ ε (v,i)))
    (hθ : ∀ d, θ (θ d) = d) (t : D → ℤ)
    (ht : ∀ d, t (θ d) = -t d) (he : ∀ v i, t (e (v,i)) = ε v*s i)
    (hconn : components σ θ = ⊤) (hp : planar σ θ)
    (u : D → A) (p : D)
    (hu : ∀ v i, e (v,i) ≠ p → vertexCorner ρ a ε (v,i) = corner σ θ u (e (v,i))) :
    vertexCorner ρ a ε (e.symm p) = corner σ θ u p := by sorry
