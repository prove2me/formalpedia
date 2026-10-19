-- Prove2me | Theorems.Thm_OAI_KervaireRibbon_cap_alignment
-- name    : OAI.KervaireRibbon.cap_alignment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:04:41.14127+00:00
-- url     : https://prove2.me/theorems/f24233c7-0396-4281-bd71-73cec9026cb6
-- title:
--   Aligning potentials across a cancelling pair
-- statement:
--   Let $A$ be a group, $I$ a nonempty finite set with a cyclic permutation $\rho$, $a:I\to A$ the relator coefficients, and $s:I\to\{1,-1\}$ the exponents with $\sum_is_i=\pm1$. Let $(\sigma,\theta)$ be planar with $\theta$ an involution and $t(\theta d)=-t(d)$. A disk atlas for a permutation $\sigma$ of darts and signs $t$ is an injection $(v,i)\mapsto\mathrm{disk}(v,i)$ of $V\times I$ into the darts with polarities $\varepsilon_v=\pm1$, such that $\sigma$ moves $\mathrm{disk}(v,i)$ to $\mathrm{disk}(v,\rho^{\varepsilon_v}i)$ and $t(\mathrm{disk}(v,i))=\varepsilon_vs_i$. The corner of a dart is $u(\theta d)\,u(\sigma d)^{-1}$ for potentials $u:D\to A$, and the vertex corner $\mathrm{vc}(v,i)$ is $a_i$ if $\varepsilon_v=1$ and $a_{\rho^{-1}i}^{-1}$ otherwise. Assume every relator corner holds for $u$. Let $x\ne y$ with $\sigma x=y$, $\sigma y\ne x$, $\theta x\ne x$, $\theta y\ne y$, $t(y)=-t(x)$, and trivial corner at $x$. Assume the $\sigma$-cycle of $x$ contains no disk dart, and every dart is a disk dart, in the $\sigma$-cycle of $x$, or fixed by both permutations. Then there are potentials $v$ with the same corners as $u$ and
--   $$
--   v(\theta y)=v(x).
--   $$
--
--   This alignment allows the cancelling pair $x,y$ to be removed from the outer boundary without changing the boundary word.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/Capping.lean#L100-L196

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
import Definitions.Def_OAI_GroupTheory_Kervaire_VertexJoin
import Definitions.Def_OAI_GroupTheory_Kervaire_Circles
import Definitions.Def_OAI_GroupTheory_Kervaire_Splicing
import Definitions.Def_OAI_GroupTheory_Kervaire_Capping

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

theorem OAI.KervaireRibbon.cap_alignment [Nonempty I]
    (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (σ θ : Perm D) (hθ : ∀ d, θ (θ d) = d) (t : D → ℤ)
    (ht : ∀ d, t (θ d) = -t d) (hp : planar σ θ)
    (b : DiskAtlas (V := V) ρ a s σ t) (u : D → A)
    (hu : ∀ v i, vertexCorner ρ a b.ε (v,i) = corner σ θ u (b.disk (v,i)))
    {x y : D} (hxy : x ≠ y) (hsx : σ x = y) (hsy : σ y ≠ x)
    (hx : θ x ≠ x) (hy : θ y ≠ y) (hpair : t y = -t x) (hcx : corner σ θ u x = 1)
    (hdisj : ∀ vi, ¬ σ.SameCycle (b.disk vi) x)
    (hcover : ∀ d, (∃ vi, b.disk vi = d) ∨ σ.SameCycle d x ∨ (σ d = d ∧ θ d = d)) :
    ∃ v : D → A, corner σ θ v = corner σ θ u ∧ v (θ y) = v x := by sorry
