-- Prove2me | Theorems.Thm_IllCondRegMem_lemma_29
-- name    : IllCondRegMem.lemma_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:54:48.299901+00:00
-- url     : https://prove2.me/theorems/6e5d347d-4c31-49b9-9e3a-d872113ec1cd
-- title:
--   Lemma 29 — Beta lower tail: $\mathbb P[X\le t]\le\big(\frac{e(a+b)}{a}t\big)^a$
-- statement:
--   Let $a,b>0$ and $X\sim\mathrm{Beta}(a,b)$. For $0\le t\le1$,
--   $$
--   \mathbb P[X\le t]\le\Big(\frac{e(a+b)}{a}\,t\Big)^{a}.
--   $$
--   In the proof of Lemma 10, the squared projection of a fixed unit vector onto a uniform random subspace is Beta-distributed, and this bound turns that into the small-probability estimate for nearly-orthogonal queries.
--
--   **Formalization Note** $\mathrm{Beta}(a,b)$ is Mathlib's `betaMeasure a b`.
--
--   Differences from the source:
--   - encoding: X ∼ Beta(a, b) → betaMeasure a b with a, b > 0; reason: Beta parameters are positive; Mathlib's measure is a probability measure exactly then
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 29, p.44 (PDF p.45)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace IllCondRegMem

/-- **Lemma 29 (Beta lower tail).**
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 29,
p.44: "For X ∼ Beta(a, b), and 0 ≤ t ≤ 1, P[X ≤ t] ≤ (e(a + b)t/a)^a."

**Formalization Note.** `Beta(a, b)` is Mathlib's `betaMeasure a b`, a probability measure for
`a, b > 0` (the parameters of a Beta law are positive). -/
theorem lemma_29 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    betaMeasure a b (Set.Iic t) ≤ ENNReal.ofReal ((Real.exp 1 * (a + b) * t / a) ^ a) := by sorry

end IllCondRegMem
