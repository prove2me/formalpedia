-- Prove2me | Theorems.Thm_OAI_KervaireRibbon_atlas_component_rigidity
-- name    : OAI.KervaireRibbon.atlas_component_rigidity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:59:29.278648+00:00
-- url     : https://prove2.me/theorems/2435d49d-28d0-4fa3-83dd-4878e3a5a9d8
-- title:
--   Corner rigidity on a component covered by relator disks
-- statement:
--   Let $A$ be a group, $I$ a nonempty finite set with a cyclic permutation $\rho$, $a:I\to A$ the relator coefficients, and $s:I\to\{1,-1\}$ the exponents with $\sum_is_i=\pm1$. Let $(\sigma,\theta)$ be a planar pair of permutations of a finite set $D$ with $\theta$ an involution, and $t:D\to\mathbb Z$ with $t(\theta d)=-t(d)$. A disk atlas for a permutation $\sigma$ of darts and signs $t$ is an injection $(v,i)\mapsto\mathrm{disk}(v,i)$ of $V\times I$ into the darts with polarities $\varepsilon_v=\pm1$, such that $\sigma$ moves $\mathrm{disk}(v,i)$ to $\mathrm{disk}(v,\rho^{\varepsilon_v}i)$ and $t(\mathrm{disk}(v,i))=\varepsilon_vs_i$. The corner of a dart is $u(\theta d)\,u(\sigma d)^{-1}$ for potentials $u:D\to A$, and the vertex corner $\mathrm{vc}(v,i)$ is $a_i$ if $\varepsilon_v=1$ and $a_{\rho^{-1}i}^{-1}$ otherwise. Let $p$ be a dart whose whole component under $\sigma$ and $\theta$ consists of disk darts. If the corner equals the vertex corner at every disk dart other than $p$, then for every $(v,i)$ with $\mathrm{disk}(v,i)=p$,
--   $$
--   \mathrm{vc}(v,i)=u(\theta p)\,u(\sigma p)^{-1}.
--   $$
--
--   So relator corner rigidity holds componentwise inside a larger diagram, for any component made only of relator disks.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/RelatorRigidity.lean#L386-L437

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

theorem OAI.KervaireRibbon.atlas_component_rigidity [Nonempty I]
    (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (σ θ : Perm D) (hθ : ∀ d, θ (θ d) = d) (t : D → ℤ)
    (ht : ∀ d, t (θ d) = -t d) (hp : planar σ θ)
    (b : DiskAtlas (V := V) ρ a s σ t) (u : D → A) (p : D)
    (hcovered : ∀ d, components σ θ p d → ∃ vi, b.disk vi = d)
    (hu : ∀ v i, b.disk (v,i) ≠ p → vertexCorner ρ a b.ε (v,i) = corner σ θ u (b.disk (v,i))) :
    ∀ vi, b.disk vi = p → vertexCorner ρ a b.ε vi = corner σ θ u p := by sorry
