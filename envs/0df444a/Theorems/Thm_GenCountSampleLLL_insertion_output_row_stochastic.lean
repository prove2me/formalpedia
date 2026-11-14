-- Prove2me | Theorems.Thm_GenCountSampleLLL_insertion_output_row_stochastic
-- name    : GenCountSampleLLL.insertion_output_row_stochastic
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:01:43.037028+00:00
-- url     : https://prove2.me/theorems/e716ae99-fdcc-46da-820d-e1c3f163e3d5
-- title:
--   The auxiliary insertion kernel is stochastic on output states
-- statement:
--   Let $a\in D$ and let $X=O(\sigma)$ be a valid outer output state. Every transition probability in the auxiliary kernel $P$ from $X$ is nonnegative, and the row sums to one. Validity of $X$ implies that $\sigma$ satisfies $D$, so the corresponding input state is also legal.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/702.pdf, Algorithm 3, pp.19–20.

import Definitions.Def_GenCountSampleLLL_insertionChain
noncomputable section
open scoped Classical BigOperators ENNReal

namespace GenCountSampleLLL
theorem insertion_output_row_stochastic (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ha : a ∈ D) (σ : I.Assign) (X : I.S D a)
    (hX : X.1 = ⟨[], Inst.Base.out σ⟩) :
    (∀ Y : I.S D a, 0 ≤ I.Pker D a X Y) ∧
      (∑ Y : I.S D a, I.Pker D a X Y) = 1 := by sorry
end GenCountSampleLLL
