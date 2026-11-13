-- Prove2me | Theorems.Thm_GenCountSampleLLL_insertion_input_row_stochastic
-- name    : GenCountSampleLLL.insertion_input_row_stochastic
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:58:54.330501+00:00
-- url     : https://prove2.me/theorems/582e21e1-ed43-43d7-bad3-a20c2368046a
-- title:
--   The auxiliary insertion kernel is stochastic on input states
-- statement:
--   Let $a\in D$, and let $X=I(\sigma)$ be a valid input state with $\sigma$ satisfying $D\setminus\{a\}$. The auxiliary kernel $P$ has nonnegative transition probabilities from $X$ and its row sums to one. This verifies the complete input-state case of stochasticity, including all three rules and the lazy step.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/702.pdf, Algorithm 3, pp.19–20.

import Definitions.Def_GenCountSampleLLL_insertionChain
noncomputable section
open scoped Classical BigOperators ENNReal

namespace GenCountSampleLLL
theorem insertion_input_row_stochastic (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ha : a ∈ D) (σ : I.Assign) (hσ : σ ∈ I.Good (D.erase a))
    (X : I.S D a) (hX : X.1 = ⟨[], Inst.Base.inp σ⟩) :
    (∀ Y : I.S D a, 0 ≤ I.Pker D a X Y) ∧
      (∑ Y : I.S D a, I.Pker D a X Y) = 1 := by sorry
end GenCountSampleLLL
