-- Prove2me | Theorems.Thm_IsRandomnessNecessaryADA_Plain_lemma_3_5
-- name    : IsRandomnessNecessaryADA.Plain.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:19:29.700776+00:00
-- url     : https://prove2.me/theorems/bdf0ed0e-881a-4763-9133-b94a0b906889
-- title:
--   Lemma 3.5 — the bit-natural query bound
-- statement:
--   There is an absolute $C>0$ with the following property. Let $n>0$, $N=20n$, and embed $[N]$ into any finite domain $X$ by an injection $e$. Let $P$ be uniform on the image of $e$, and let $m$ be any deterministic bit-natural mechanism on $X$. Set
--   $$k=\left\lceil\log_{10/9}(N^n)\right\rceil+1\le Cn\log_2N.$$
--   There exists a deterministic adaptive Boolean-query analyst $A$ such that for every ordered row tuple $s\in[N]^n$, the actual interaction on sample $(e(s_t))_t$ has an answer $a_j$ with
--   $$|a_j-Pq_j|>1/10\qquad\text{for some }j\le k.$$
--   The analyst has history access only. This pathwise attack implies the probability-accuracy impossibility in the source and applies to the entire bit-natural class, including mechanisms whose real answers vary while their threshold bits agree. The embedding covers the larger-domain case explicitly allowed at the start of Section 3.
--
--   Differences from the source:
--   - encoding: one-based finite sets and ordered datasets → Fin indices and function tuples, with full real answers; reason: reindexing preserves every query, ordered sample with repetition, and response
--   - generalization: a bit-natural mechanism cannot remain 0.1-accurate beyond O(n log N) queries → one analyst forces error on every support-valued ordered sample within the exact horizon, with an absolute asymptotic bound; reason: the pathwise shrinking argument on p.9 gives this stronger guarantee, which implies failure of the Definition 2.2 probability guarantee
-- source:
--   Edith Cohen, Haim Kaplan, Yishay Mansour, Shay Sapir, Uri Stemmer, Eliad Tsfadia, STOC 2027 submission #267 (October 2026), Lemma 3.5 and Remark 3.4, p.9; §3, pp.8–9; exact horizon §4.2, p.10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/267.pdf; PDF/printed pages coincide.

import Definitions.Def_IsRandomnessNecessaryADA_Plain_Survivors

set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain

/-- Lemma 3.5, p.9: the full bit-natural class, and the pathwise bound from pp.9–10. -/
theorem lemma_3_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type} [Fintype X] (n : ℕ) (hn : 0 < n)
      (e : Fin (20 * n) ↪ X) (m : Mechanism X n), IsBitNatural m →
      (attackHorizon n (20 * n) : ℝ) ≤ C * n * (Real.log (20 * n) / Real.log 2) ∧
      ∃ A : BooleanAnalyst X, ∀ s : Fin n → Fin (20 * n),
        interaction m (liftAnalyst A) (fun t => e (s t)) (attackHorizon n (20 * n)) ∈
          errorEvent (uniformSupport (by omega) e) (1 / 10) := by sorry

end IsRandomnessNecessaryADA.Plain
