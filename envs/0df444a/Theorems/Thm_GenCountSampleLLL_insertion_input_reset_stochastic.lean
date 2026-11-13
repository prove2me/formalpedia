-- Prove2me | Theorems.Thm_GenCountSampleLLL_insertion_input_reset_stochastic
-- name    : GenCountSampleLLL.insertion_input_reset_stochastic
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:55:45.445193+00:00
-- url     : https://prove2.me/theorems/d0249a79-f310-4301-9ad9-21fa586ff43b
-- title:
--   The input RESET rule is stochastic
-- statement:
--   If $a\in D$ and an input assignment $\sigma$ satisfies $D\setminus\{a\}$, then the RESET rule at $I(\sigma)$ defines a probability distribution on the recursively constructed insertion-chain state space. In particular, every transition probability is nonnegative and the row sums to one. This verifies the random-list input case of the auxiliary kernel’s stochasticity.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/702.pdf, Algorithm 3, pp.19–20.

import Definitions.Def_GenCountSampleLLL_insertionChain
noncomputable section
open scoped Classical BigOperators ENNReal

namespace GenCountSampleLLL
theorem insertion_input_reset_stochastic (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ha : a ∈ D) (σ : I.Assign) (hσ : σ ∈ I.Good (D.erase a)) :
    (∀ Y : I.S D a, 0 ≤ I.iRule D a σ Rule.reset Y.1) ∧
      (∑ Y : I.S D a, I.iRule D a σ Rule.reset Y.1) = 1 := by sorry
end GenCountSampleLLL
