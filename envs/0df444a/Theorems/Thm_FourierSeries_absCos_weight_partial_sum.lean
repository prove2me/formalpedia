-- Prove2me | Theorems.Thm_FourierSeries_absCos_weight_partial_sum
-- name    : FourierSeries.absCos_weight_partial_sum
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:54:24.299317+00:00
-- url     : https://prove2.me/theorems/94a864c8-ecde-445f-8435-672c7925aa64
-- title:
--   A closed form for $\sum_{m\le M} 1/(4m^2-1)$
-- statement:
--   **An exact evaluation of a partial sum of reciprocal odd-square-differences.**
--
--   For every $M \ge 0$,
--
--   $$\sum_{m=1}^{M} \frac{1}{4m^{2}-1} \;=\; \frac{M}{2M+1} .$$
--
--   This is an identity, not an estimate: the sum telescopes exactly. Writing
--   $4m^{2}-1 = (2m-1)(2m+1)$ and splitting into partial fractions,
--
--   $$\frac{1}{4m^{2}-1} = \frac{1}{2}\left(\frac{1}{2m-1}-\frac{1}{2m+1}\right),$$
--
--   all interior terms cancel and the sum collapses to
--   $\tfrac12\bigl(1 - \tfrac{1}{2M+1}\bigr) = \tfrac{M}{2M+1}$.
--
--   Letting $M \to \infty$ recovers the classical $\sum_{m\ge1}\tfrac{1}{4m^2-1} = \tfrac12$. The
--   finite form is the one that matters in practice: it gives the exact partial sum of the
--   coefficient weights in the Fourier expansion of $|\cos\theta|$, whose $m$-th coefficient is
--   $\tfrac{4}{\pi}\cdot\tfrac{(-1)^{m+1}}{4m^2-1}$, and hence an exact rather than asymptotic
--   truncation error.
--
--   **Formalization note.** The sum runs over `Finset.Icc 1 Mcut`, so $M = 0$ gives the empty sum
--   $0$, consistent with the right-hand side.
-- source:
--   Classical telescoping identity. Lean proof extracted from `Salt/MR/AbsCosFourier.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace FourierSeries

theorem absCos_weight_partial_sum (Mcut : ℕ) :
    ∑ m ∈ Finset.Icc 1 Mcut, (1 : ℝ) / (4 * (m : ℝ) ^ 2 - 1)
      = (Mcut : ℝ) / (2 * (Mcut : ℝ) + 1) := by sorry

end FourierSeries
