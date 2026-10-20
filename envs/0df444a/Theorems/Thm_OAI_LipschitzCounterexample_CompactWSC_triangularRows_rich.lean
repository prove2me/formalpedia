-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_triangularRows_rich
-- name    : OAI.LipschitzCounterexample.CompactWSC.triangularRows_rich
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:23:47.655698+00:00
-- url     : https://prove2.me/theorems/f9919db1-cbc7-47d1-ad2b-065c8fb13f9d
-- title:
--   A non-convergent weakly Cauchy sequence gives rich triangular rows
-- statement:
--   Triangular rows are finite sequences of pairs (smooth $1$-Lipschitz test $f_j$ with $f_j(0)=0$, molecular data $a_i$ supported in $K$ of cost $\le C$ and within $\rho$ of the sequence $\mu$) with $\langle a_i,f_j\rangle\ge4\alpha$ for $j\le i$ and $|\langle a_i,f_j\rangle|\le\alpha$ for $i<j$, where $\langle a,f\rangle=\sum_ic_i(f(p_i)-f(q_i))$. A family of rows is rich if it contains rows of every length. Let $K\ni0$ be a subset of a Hilbert space and $u_n$ a sequence in $\mathcal F_K(H)$ with $\|u_n\|\le C$. Suppose $u_n$ converges weak$^*$ to $\varphi$, with $\varphi$ at distance at least $d$ from $\mathcal F_K(H)$ in its bidual. If $\rho\le\alpha/4$ and $32\alpha\le d$, then
--   $$
--   \text{the triangular rows for }(K,C,\rho,\alpha,u)\text{ are rich}.
--   $$
--
--   Rich triangular rows are the combinatorial witness of non-convergence used in the compact case.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/SmoothRows.lean#L112-L159

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBlocks
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothHilbert
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MolecularApproximation
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothCalculus
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_EnergyEstimates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothRows

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
universe uH
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupSpace
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealSpace
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupSubtypeSpaceMemSubmoduleRealSupported
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealSubtypeSpaceMemSubmoduleSupported
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeSpaceMemSubmoduleSupported
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealContinuousLinearMapIdSubtypeSpaceMemSubmoduleSupported
variable {H : Type uH} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

theorem OAI.LipschitzCounterexample.CompactWSC.triangularRows_rich {K : Set H} (h0 : (0:H) ∈ K)
    (u : ℕ → supported K) (φ : ((supported K) →L[ℝ] ℝ) →L[ℝ] ℝ)
    (hφ : ∀ f, Tendsto (fun n => f (u n)) atTop (𝓝 (φ f)))
    {d C ρ α : ℝ} (hd : 0 < d) (hC : 0 < C) (hρ : 0 < ρ) (hα : 0 < α)
    (hρα : ρ ≤ α/4) (hαd : 32*α ≤ d) (hu : ∀ n, ‖u n‖ ≤ C)
    (hfar : ∀ x : supported K, d ≤ @norm (((supported K) →L[ℝ] ℝ) →L[ℝ] ℝ) inferInstance (φ-NormedSpace.inclusionInDoubleDual ℝ (supported K) x)) :
    (triangularRows K C ρ α (fun n => (u n : Space H))).Rich := by sorry
