-- Prove2me | Theorems.Thm_OrderSelProphet_Kernel_lemma_F_2
-- name    : OrderSelProphet.Kernel.lemma_F_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:59:42.036048+00:00
-- url     : https://prove2.me/theorems/4e680652-80fd-4bea-9964-eee60bde35e9
-- title:
--   Lemma F.2 — load representation: $\ell_{\Gamma_1}(K_1,\lambda)\le\bar\ell_\lambda=\Gamma_1+\int_0^\infty\sigma(r)(r-k(r))R(r)/D(r)^2\,dr$
-- statement:
--   For every $\lambda\in\Lambda$, with $\bar\ell_\lambda=\ell_{\Gamma_1}(K_1,\lambda)+\Gamma_1Y(0)$ (92),
--   $$\ell_{\Gamma_1}(K_1,\lambda)\le\bar\ell_\lambda=\Gamma_1+\int_0^\infty\frac{\sigma(r)\,(r-k(r))\,R(r)}{D(r)^2}\,dr,\quad(93)$$
--   where $D=D_{\Gamma_1}$, $Y(r)=y_{K_1,\lambda}(t_r)$, $\sigma(r)=S_{K_1,\lambda}(t_r)$, $k(r)=e^r\frac{d}{dr}B_{K_1,\lambda}(t_r)$ and $R(r)=e^r(1-Y(r))$.
--
--   Differences from the source:
--   - encoding: Λ: measurable λ : [0,1] → [0,1], identified when equal a.e. → Profile: measurable functions ℝ → ℝ with values in [0,1] on [0,1]; quantifying over representatives; reason: every quantity depends only on the a.e. class on [0,1]; a measurable function on [0,1] extends measurably to ℝ
--   - encoding: ℓ̄_λ and ℓ_{Γ1}(K1, λ) real → both in ℝ≥0∞; the identity as auxLoad = ENNReal.ofReal(Γ1 + ∫_{(0,∞)} …); reason: loads are nonnegative; the right side is a nonnegative real
--   - encoding: k(r) := e^r d/dr B(t_r) = r B′(t_r) (a.e.) → kRate λ r = exp r · deriv (s ↦ B(t_s)) r; reason: the first printed form; the two agree a.e.
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), Lemma F.2, p. 50

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Certificate

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-- Lemma F.2 (Load representation), p. 50. -/
theorem lemma_F_2 (lam : Profile) :
    loadK Gamma1 K1 lam.1 ≤ auxLoad lam.1 ∧
      auxLoad lam.1 = ENNReal.ofReal (Gamma1 + ∫ r in Ioi (0 : ℝ),
        sigmaC lam.1 r * (r - kRate lam.1 r) * Rc lam.1 r / Dc r ^ 2) := by sorry

end OrderSelProphet.Kernel
