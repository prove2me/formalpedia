-- Prove2me | Theorems.Thm_FourierSeries_hasSum_absCos_tail_weights
-- name    : FourierSeries.hasSum_absCos_tail_weights
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:26:06.035271+00:00
-- url     : https://prove2.me/theorems/f7f75fe4-852c-4451-8426-e8616dfdac13
-- title:
--   The telescoping tail of the $|\cos|$ Fourier coefficients
-- statement:
--   **An exactly summable tail of reciprocal odd-square-differences.**
--
--   For every $M \ge 0$,
--
--   $$\sum_{k=0}^{\infty} \frac{1}{4(M+k+1)^{2}-1} \;=\; \frac{1}{2(2M+1)} .$$
--
--   The summand factors as a difference of reciprocals of consecutive odd numbers,
--
--   $$\frac{1}{4m^{2}-1} = \frac{1}{(2m-1)(2m+1)}
--   = \frac{1}{2}\left(\frac{1}{2m-1} - \frac{1}{2m+1}\right),$$
--
--   so the series **telescopes**: the partial sums collapse to
--   $\tfrac12\bigl(\tfrac{1}{2M+1} - \tfrac{1}{2(M+K)+1}\bigr)$, and letting $K \to \infty$ leaves
--   exactly $\tfrac{1}{2(2M+1)}$.
--
--   At $M = 0$ this is the classical evaluation $\sum_{m\ge1}\tfrac{1}{4m^2-1} = \tfrac12$. The
--   general $M$ form is what gives the *exact* truncation error for the Fourier series of
--   $|\cos\theta|$, whose coefficients are $\tfrac{4}{\pi}\cdot\tfrac{(-1)^{m+1}}{4m^2-1}$ — the
--   tail bound $\tfrac{2}{\pi(2M+1)}$ is this identity multiplied by $4/\pi$.
--
--   **Formalization note.** The statement is a `HasSum`, so it asserts unconditional summability to
--   the stated value, which is available here because all terms are positive.
-- source:
--   Classical telescoping series. Lean proof extracted from `Salt/MR/AbsCosFourier.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace FourierSeries

theorem hasSum_absCos_tail_weights (Mcut : ℕ) :
    HasSum (fun k : ℕ => 1 / (4 * ((Mcut : ℝ) + (k : ℝ) + 1) ^ 2 - 1))
      (1 / (2 * (2 * (Mcut : ℝ) + 1))) := by sorry

end FourierSeries
