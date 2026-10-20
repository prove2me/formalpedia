-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_SeparatingStages_support_disjoint
-- name    : OAI.LipschitzCounterexample.SeparatingStages.support_disjoint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:31:37.806462+00:00
-- url     : https://prove2.me/theorems/3d221c82-a255-4635-a40c-94f964060325
-- title:
--   Separated cube points have disjointly supported bump vectors
-- statement:
--   For $k>0$ and points $s,t\in[-1,1]^k$, let $\hat G_k(s)$ be the normalized bump vector with entries proportional to $\prod_j\psi(ks_j-a_j)$, indexed by integer labels $a\in\{-k,\dots,k\}^k$, where $\psi$ is positive exactly on $(-1,1)$. If some coordinate satisfies $|s_j-t_j|>2/k$, then for every label $a$,
--   $$
--   \hat G_k(s)_a=0\quad\text{or}\quad\hat G_k(t)_a=0 .
--   $$
--
--   This is how distinct points eventually receive orthogonal slot vectors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/SeparatingCoordinates.lean#L101-L115

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.SeparatingStages
universe uIndex uOtherIndex
open scoped BigOperators InnerProductSpace Topology ENNReal

theorem OAI.LipschitzCounterexample.SeparatingStages.support_disjoint {k : ℕ} (hk : 0 < k) {s t : CubeSpace k} (j : Fin k)
    (hst : 2/(k : ℝ) < |s j-t j|) (a : Label k) :
    normalized k s a = 0 ∨ normalized k t a = 0 := by sorry
