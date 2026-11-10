-- Prove2me | Theorems.Thm_IntegerSumAmplification_Main_lemma_6_6
-- name    : IntegerSumAmplification.Main.lemma_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:04:52.913347+00:00
-- url     : https://prove2.me/theorems/fb9f5b7a-1929-4449-88b0-63658796ed79
-- title:
--   Lemma 6.6 — Order statistics in linear size
-- statement:
--   There is an absolute constant $C>0$ such that for every pair of positive integers $L,w$ and every rank $1\le j\le L$, a bounded-fan-in Boolean circuit computes the $j$-th smallest of $L$ unsigned $w$-bit words, including repetitions, using at most $CLw$ gates. The circuit is correct for every input tuple.
--
--   There also exists a circuit of at most $CLw$ gates which receives both the words and the rank as inputs and is correct for every valid rank. The rank input encodes $j-1$ in $\lceil\log_2 L\rceil$ bits; at $L=1$ it has zero bits. The same absolute constant works for both clauses, independent of $L,w,j$.
--
--   Differences from the source:
--   - encoding: bounded-fan-in Boolean circuits and oracle calls → well-formed LowDepthPRF circuits, actual gate counts and actual evaluation, without a depth restriction; reason: the published syntax has the source gate basis, free wiring and fan-out
--   - encoding: absolute O and Ω constants → positive real constants existentially quantified before every problem parameter; reason: this spells out uniform asymptotic bounds without introducing parameter-dependent constants
--   - encoding: unsigned words and a binary rank j in 1 through L → little-endian words and the code j-1 in ceil(log₂ L) bits; reason: every valid rank is represented, including j=L and the zero-bit singleton case
-- source:
--   Farhan Ali and Weiqiang Yuan, Optimal Black-Box Hardness Amplification for Integer Sums, held manuscript dated November 3, 2026 (STOC 2027 submission; acceptance not asserted); citation_basis: published. Lemma 6.6, printed p. 17 / PDF p. 20; proof continues printed p. 18 / PDF p. 21. PDF SHA256 181fd8ae5069b0c062ebccc0aa72d5a78ec0c836e6d8f6f99dd60464c0b746d7.

import Definitions.Def_IntegerSumAmplification_Main_CircuitPrediction

namespace IntegerSumAmplification.Main

theorem lemma_6_6 : ∃ C : ℝ, 0 < C ∧ ∀ L w : ℕ, 0 < L → 0 < w →
    (∀ j : ℕ, 1 ≤ j → j ≤ L →
      ∃ S : LowDepthPRF.Circuit 0 0 (L * w) w,
        S.WF ∧ (S.size : ℝ) ≤ C * L * w ∧
        ∀ a : Fin L → Bits w, decode (S.evalPlain (pack a)) =
          orderStatistic (fun i => decode (a i)) j) ∧
    (∃ S : LowDepthPRF.Circuit 0 0 (L * w + wordWidth L) w,
      S.WF ∧ (S.size : ℝ) ≤ C * L * w ∧
      ∀ (a : Fin L → Bits w) (j : ℕ), 1 ≤ j → j ≤ L →
        decode (S.evalPlain (joinBits (pack a) (encode (wordWidth L) (j - 1)))) =
          orderStatistic (fun i => decode (a i)) j) := by sorry

end IntegerSumAmplification.Main
