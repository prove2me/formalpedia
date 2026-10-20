-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_schur
-- name    : OAI.LipschitzCounterexample.WeakSequences.schur
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:25:44.039191+00:00
-- url     : https://prove2.me/theorems/ffc5d998-15ec-4936-aec3-87ed2a067130
-- title:
--   Schur's theorem: weakly null sequences in ℓ¹ are norm null
-- statement:
--   Let $u_n$ be a sequence in real $\ell^1$ such that $f(u_n)\to0$ for every bounded linear functional $f$. Then
--   $$
--   \|u_n\|_1\to0 .
--   $$
--
--   This is Schur's property of $\ell^1$: weak and norm convergence of sequences coincide.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/Schur.lean#L140-L229

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.WeakSequences
universe uE uF
open Filter Topology
open scoped ENNReal NNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem OAI.LipschitzCounterexample.WeakSequences.schur {u : ℕ → RealL1} (hu : WeakNull u) : Tendsto u atTop (𝓝 0) := by sorry
