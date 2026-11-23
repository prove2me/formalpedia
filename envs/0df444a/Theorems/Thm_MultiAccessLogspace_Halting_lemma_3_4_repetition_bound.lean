-- Prove2me | Theorems.Thm_MultiAccessLogspace_Halting_lemma_3_4_repetition_bound
-- name    : MultiAccessLogspace.Halting.lemma_3_4_repetition_bound
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:43:52.371644+00:00
-- url     : https://prove2.me/theorems/b3aafc4f-ffb0-4cab-ba84-5dfb0ea0c41e
-- title:
--   Lemma 3.4 — backward repetition probability
-- statement:
--   Let $H_0,\ldots,H_{N-1}$ be independent, identically distributed measurable variables with values in $\mathbb N\cup\{\infty\}$, and suppose $P(H_i=h)=2^{-h}$ for $1\le h\le d$. Fix a coordinate $j$ and let $b\ge1$. The event $\operatorname{HasRepeatedBeforeGreater}(b,d,H,j)$ asserts that for some $h\in[d]$, there is an interval ending at $j$ which contains no value larger than $h$ and contains at least $b$ occurrences of $h$. Its probability satisfies
--   $$
--   P\bigl(\operatorname{HasRepeatedBeforeGreater}(b,d,H,j)\bigr)\le 2^{-(b-1)}.
--   $$
--
--   For a fixed $h$, condition on $H_j=h$ and scan $H_{j-1},H_{j-2},\ldots$ backwards. Ignoring values below $h$, the next relevant value is equally likely to equal $h$ or exceed $h$, since both have mass $2^{-h}$. Hence $b-1$ earlier occurrences of $h$ can precede every larger value with probability at most $2^{-(b-1)}$. Summing the disjoint cases $H_j=h$ over $h\in[d]$ gives the displayed aggregate bound. This supplies the second term in Lemma 3.4 without an additional factor of $d$.
--
--   **Formalization Note.** The interval formulation is finite, so no infinite stopping-time measurability is built into the statement. Independence and identical distribution are used only for the finitely many coordinates preceding $j$ and for $j$ itself.
-- source:
--   William M. Hoza, STOC 2027 submission #92 (October 2026), Lemma 3.4 proof, backward-scanning argument, PDF p. 7 (printed p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/92.pdf; PDF SHA-256 92de35889559d87b5a77d83317b9c7b2c8924912fbd5c712f2af3c005c8998d8

import Mathlib
import Definitions.Def_MultiAccessLogspace_Halting_Rulers
import Definitions.Def_MultiAccessLogspace_Halting_HyporulerEvents

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultiAccessLogspace.Halting

/-- At each fixed coordinate, the probability of seeing `b` equal values in a greater-free
interval ending there is at most `2⁻⁽ᵇ⁻¹⁾`, after taking the union over values in `[d]`. -/
theorem lemma_3_4_repetition_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d b N : ℕ) (hb : 1 ≤ b)
    (H : Fin N → Ω → ℕ∞) (hmeas : ∀ i, Measurable (H i))
    (hindep : iIndepFun H P)
    (hident : ∀ i j, IdentDistrib (H i) (H j) P P)
    (hmass : ∀ i, ∀ h : ℕ, 1 ≤ h → h ≤ d →
      P {ω | H i ω = (h : ℕ∞)} = (2 : ℝ≥0∞)⁻¹ ^ h) (j : Fin N) :
    P {ω | HasRepeatedBeforeGreater b d H j ω} ≤ (2 : ℝ≥0∞)⁻¹ ^ (b - 1) := by sorry
