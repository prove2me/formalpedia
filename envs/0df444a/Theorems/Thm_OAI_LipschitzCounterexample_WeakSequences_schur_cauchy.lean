-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_schur_cauchy
-- name    : OAI.LipschitzCounterexample.WeakSequences.schur_cauchy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:26:23.747655+00:00
-- url     : https://prove2.me/theorems/fd198ad5-458b-4f9a-9acb-9d7a79f90e47
-- title:
--   Weakly Cauchy sequences in ℓ¹ are norm Cauchy
-- statement:
--   Let $u_n$ be a sequence in real $\ell^1$ such that $(f(u_n))_n$ is Cauchy for every bounded linear functional $f$. Then $(u_n)$ is Cauchy in norm:
--   $$
--   \|u_n-u_m\|_1\to0\quad(n,m\to\infty).
--   $$
--
--   In particular $\ell^1$ is weakly sequentially complete.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/WeakSums.lean#L29-L47

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.WeakSequences
universe uE uF uG
open Filter Topology
open scoped ENNReal NNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem OAI.LipschitzCounterexample.WeakSequences.schur_cauchy {u : ℕ → RealL1} (hu : WeakCauchy u) : CauchySeq u := by sorry
