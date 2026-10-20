-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_SeparatingStages_stage_coord_zero
-- name    : OAI.LipschitzCounterexample.SeparatingStages.stage_coord_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:33:49.69964+00:00
-- url     : https://prove2.me/theorems/c58ba3a7-9aab-4fa1-b48b-8e877a79123b
-- title:
--   Stage vectors vanish on labels of other stages
-- statement:
--   Let $M=U\oplus_2\ell^2$ with $U=\bigl(\bigoplus_n\mathbb R^{\mathrm{BlockLabel}(n)}\bigr)_{\ell^2}$, where block $n$ has a reserved label and, for each stage $k\le n$, a copy of the stage-$(k+1)$ labels. The slot vector $\mathrm{slot}_n(x)$ is the unit vector obtained by rotating through the stage vectors of block $n$ with angles driven by the slot radius of $x$; the stage-$k$ vectors are normalized bump vectors $G_{k+1}(p(x))$ of the coordinates $p_j(x)=\tanh(x_{(j)})$. The stage-$j$ vector of block $n$ vanishes at every label $a$ whose stage index differs from $j$:
--   $$
--   j\ne\mathrm{stage}(a)\ \Longrightarrow\ \mathrm{stage}_{n,j}(x)_a=0 .
--   $$
--
--   So stage vectors of different stages are orthogonal and supported on disjoint label sets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/LocalOrthogonality.lean#L19-L36

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.SeparatingStages
universe uI
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set

theorem OAI.LipschitzCounterexample.SeparatingStages.stage_coord_zero (n j : ℕ) (x : M) (a : BlockLabel n)
    (hj : j ≠ stageIndex a) : stage n j x a = 0 := by sorry
