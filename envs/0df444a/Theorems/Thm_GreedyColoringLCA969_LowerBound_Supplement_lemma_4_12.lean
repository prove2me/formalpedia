-- Prove2me | Theorems.Thm_GreedyColoringLCA969_LowerBound_Supplement_lemma_4_12
-- name    : GreedyColoringLCA969.LowerBound.Supplement.lemma_4_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T21:35:21.064534+00:00
-- url     : https://prove2.me/theorems/d4095352-2cac-4abd-8c8b-52ec6d768026
-- title:
--   Lemma 4.12 — The non-increasing recursion F_i(ε) ≤ a log(1/ε) F_{i−1}(ε^a) has the exact triangular-exponent solution.
-- statement:
--   Let $t\ge1$ be an integer and $a\ge1$ a real number. For each $i=1,\ldots,t$, let $F_i:(0,1/2]\to\mathbb Z_+$ be non-increasing. For every $\varepsilon$ in this domain assume
--
--   $$F_1(\varepsilon)\le a\log_2(1/\varepsilon),\qquad
--   F_i(\varepsilon)\le a\log_2(1/\varepsilon)F_{i-1}(\varepsilon^a)\quad(2\le i\le t).$$
--
--   Then, throughout the same domain,
--
--   $$F_t(\varepsilon)\le a^{t(t+1)/2}(\log_2(1/\varepsilon))^t.$$
--
--   The exponent is the exact triangular integer, and $\varepsilon^a$ is real exponentiation. This solves the recurrence used in the finite-label query analysis.
--
--   Differences from the source:
--   - encoding: indices 1 through t and recurrence evaluated at epsilon^a → indices Fin t and recurrence quantified over domain elements epsilon,eta with eta=epsilon^a; reason: index i denotes source index i+1; for a>=1 and 0<epsilon<=1/2 the real power epsilon^a is in the domain, so every required recurrence evaluation occurs
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), p. 22 (PDF 23), Lemma 4.12

import Definitions.Def_GreedyColoringLCA969_LowerBound_GraphBasics

open scoped ENNReal BigOperators
open MeasureTheory Classical
set_option autoImplicit false

namespace GreedyColoringLCA969.LowerBound.Supplement

theorem lemma_4_12 (t : ℕ) (ht : 1 ≤ t) (a : ℝ) (ha : 1 ≤ a)
    (F : Fin t → Set.Ioc (0 : ℝ) (1 / 2) → ℕ+)
    (hmono : ∀ i, Antitone (F i))
    (hbase : ∀ (i : Fin t), i.val = 0 → ∀ ε, (F i ε : ℝ) ≤ a * log2 (1 / ε.val))
    (hrec : ∀ (i j : Fin t), j.val + 1 = i.val →
      ∀ (ε η : Set.Ioc (0 : ℝ) (1 / 2)), η.val = ε.val ^ a →
        (F i ε : ℝ) ≤ a * log2 (1 / ε.val) * (F j η : ℝ)) :
    ∀ (i : Fin t), i.val + 1 = t → ∀ ε,
      (F i ε : ℝ) ≤ a^(t * (t + 1) / 2) * (log2 (1 / ε.val))^t := by sorry

end GreedyColoringLCA969.LowerBound.Supplement
