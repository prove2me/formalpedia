-- Prove2me | Theorems.Thm_LRTempElim_sech_second_moment
-- name    : LRTempElim.sech_second_moment
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:25:50.076234+00:00
-- url     : https://prove2.me/theorems/4f32ee0c-7e41-4fc3-b39a-63ddbc94d0df
-- title:
--   §B.4.6: $\int_{\mathbb R}u^2\operatorname{sech}u\,du=\pi^3/4$
-- statement:
--   The second moment of the hyperbolic secant is
--   $$
--   \int_{-\infty}^{\infty}u^2\operatorname{sech}(u)\,du=\frac{\pi^3}{4}.
--   $$
--
--   This constant fixes the leading coefficient in the asymptotics (136) of the logistic slope information.
--
--   **Formalization Note** $\operatorname{sech}u=1/\cosh u$; the integral is a Lebesgue integral over $\mathbb R$ (the range of the substitution $u=ax/2$ in (147)). Since $\pi^3/4\ne0$, the identity also certifies integrability.
--
--   Differences from the source:
--   - encoding: ∫ u² sech(u) du (range from the substitution u = ax/2 over ℝ) → Bochner integral over ℝ of u² (cosh u)⁻¹; reason: definition of sech; the substitution maps ℝ onto ℝ
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), §B.4.6, p.45 (pdf p.47)

import Mathlib

namespace LRTempElim

/-- **`∫ u² sech u du = π³/4`** (§B.4.6). Chen, Wu, Yang, Zeng, *Likelihood-Ratio Learning under
Weak Overlap via Analytic Temporal Elimination*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 eee65139…), §B.4.6, p.45 (pdf p.47).

"As `a → ∞`, `e^{−2u²/a²} → 1` and `∫ u² sech(u) du = π³/4`"

**Formalization Note.** The integral is over `ℝ` (the range of the substitution `u = ax/2` in
eq. (147)); `sech u = (Real.cosh u)⁻¹`. Since `π³/4 ≠ 0`, the identity also excludes a junk
value of a non-integrable integrand. -/
theorem sech_second_moment :
    ∫ u : ℝ, u ^ 2 * (Real.cosh u)⁻¹ = Real.pi ^ 3 / 4 := by sorry

end LRTempElim
