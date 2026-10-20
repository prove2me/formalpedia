-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_LocalGeometry_badSet_finite
-- name    : OAI.LipschitzCounterexample.LocalGeometry.badSet_finite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:46:25.479864+00:00
-- url     : https://prove2.me/theorems/087596de-76a5-41a3-a45c-0e34883a6e89
-- title:
--   Points of large local Lipschitz constant are finitely many
-- statement:
--   Let $\mathcal H=\bigl(\bigoplus_n\mathbb R^{\iota_n}\bigr)_{\ell^2}$ be a Hilbert sum of finite-dimensional Euclidean spaces, with coordinates indexed by pairs $(n,a)$; for a set $S$ of coordinates, $P_S$ is the orthogonal projection onto vectors supported in $S$. A map $D:M\to\mathcal H$ is locally orthogonal if for finitely many distinct points $z_i$ there are $r>0$, a block index $l$ and pairwise disjoint coordinate sets $S_i$ with $\mathrm{tail}_l(D(x))$ supported in $S_i$ whenever $d(x,z_i)<r$. Let $D$ be $L$-Lipschitz ($L>0$) and locally orthogonal, and let $b_i\in\mathcal H$ with $\|b_i\|\le1$ and every coordinate of $b_i$ tending to $0$. Let $(O_j)$ be a base of the topology of $M$, and suppose the best Lipschitz constants $a_j$ of $x\mapsto\langle D(x),b_i\rangle$ on $O_j$ converge as $i\to\infty$. Then for each $\eta>0$ the bad set is finite:
--   $$
--   \#\{z\in M:\ a_j\ge\eta\ \text{for every }j\text{ with }z\in O_j\}<\infty .
--   $$
--
--   So the scalar tests $\langle D(\cdot),b_i\rangle$ are asymptotically flat away from finitely many points.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/LocalLipschitz.lean#L158-L206

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalGeometry
universe uM uN uB uIndex
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open CoordinateSpaces LocalLipschitz
variable {M : Type uM} [MetricSpace M] {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

theorem OAI.LipschitzCounterexample.LocalGeometry.badSet_finite (D : M → Hilbert (ι := ι)) {L : ℝ≥0} (hL : 0 < L)
    (hD : LipschitzWith L D) (hloc : LocalOrthogonality D)
    (b : ℕ → Hilbert (ι := ι)) (hbn : ∀ i, ‖b i‖ ≤ 1)
    (hb : ∀ a : Σ n, ι n, Tendsto (fun i => b i a.1 a.2) atTop (𝓝 0))
    {B : Type uB} (O : B → Set M)
    (hbase : ∀ z : M, ∀ r : ℝ, 0 < r → ∃ j, z ∈ O j ∧ O j ⊆ Metric.ball z r)
    (a : B → ℝ)
    (ha : ∀ j, Tendsto (fun i => constant (fun x => ⟪D x,b i⟫_ℝ) (O j)) atTop (𝓝 (a j)))
    {η : ℝ} (hη : 0 < η) : (badSet O a η).Finite := by sorry
