-- Prove2me | Theorems.Thm_NonadaptiveSFT_lemma_23
-- name    : NonadaptiveSFT.lemma_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:00.2863+00:00
-- url     : https://prove2.me/theorems/43ac7489-f3f3-4c5a-8ba9-8af564237fa4
-- title:
--   Lemma 23 — total query count $Q_{total}=O(s\log N\log s)$
-- statement:
--   For $2\le s<N$, the total number of query occurrences $Q_{total}$ of the nonadaptive query sets, given by (50), satisfies
--
--   $$Q_{total}=O(s\log N\log s)$$
--
--   with an absolute constant.
--
--   This is the query bound (35) of Theorem 15, and through it the query bound (4) of Theorem 1.
--
--   Differences from the source:
--   - encoding: ⌈log m⌉ for integers m ≥ 1 → Nat.clog 2 m; reason: same value
--   - encoding: O(·) → an absolute constant C chosen before a, d, s; reason: the meaning of O(·)
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), Lemma 23, (49), (50), p.40 (PDF p.42)

import Mathlib
import Definitions.Def_NonadaptiveSFT_Recovery

namespace NonadaptiveSFT

/-- **Lemma 23** (Total query count), p.40 (PDF p.42).

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…); (49), (50), p.40, with (19), (21), (36), (43).

`Q_total = O(s log N log s)`.

**Formalization Note.** `Q_total` is the closed-form natural number (50), `NonadaptiveSFT.Qtotal`,
with every ceiling of the page. "Throughout this section, s is a fixed integer with 2 ≤ s < N"
(p.39). `O(·)` is an absolute constant `C` chosen before `a`, `d`, `s`; `log = log₂`, `log N = a·d`. -/
theorem lemma_23 :
    ∃ C : ℝ, 0 < C ∧ ∀ (a d s : ℕ), 1 ≤ a → 1 ≤ d → 2 ≤ s → s < 2 ^ (a * d) →
      (Qtotal s a d : ℝ) ≤ C * s * ((a * d : ℕ) : ℝ) * Real.logb 2 s := by sorry

end NonadaptiveSFT
