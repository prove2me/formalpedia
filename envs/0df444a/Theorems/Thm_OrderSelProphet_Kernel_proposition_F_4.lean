-- Prove2me | Theorems.Thm_OrderSelProphet_Kernel_proposition_F_4
-- name    : OrderSelProphet.Kernel.proposition_F_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:59:42.557852+00:00
-- url     : https://prove2.me/theorems/806531a9-c18f-4d45-8335-c98915ab860e
-- title:
--   Proposition F.4 — regional Bellman certificate: under (113), (114), (121) and the terminal condition, $\bar\ell_\lambda\le\Gamma_1+T_0(0)+W(0)-P(0,0)$
-- statement:
--   Fix a parameter box $\mathcal R$, a regional bound $\mathcal U_{\mathcal R}(r,x,h)$, a correction term $\mathcal G(r,x,h)$, a continuous piecewise-bilinear function $P(r,h)$ on a finite grid, an absolutely continuous $W$ and a number $\bar V$, and put $\mathcal V(r,h)=T_0(r)+W(r)-P(r,h)$. Suppose that (113) $R(r)+\Xi_+(r)\le\mathcal U_{\mathcal R}(r,x(\lambda),h(r))$ and (114) $\int_0^{b_4}\sigma(r)(r-k(r))\Xi_+(r)/D(r)^2\,dr\ge\int_0^{b_4}\sigma(r)(1-\lambda(u_r))\mathcal G(r,x(\lambda),h(r))\,dr$ hold for every $\lambda\in\Lambda(\mathcal R)$, that $V_\lambda(b_4)\le\bar V$ uniformly on the region, and that for almost every $r\in[0,b_4]$
--   $$-W'(r)\ge\sup_{(x,h)\in\mathcal D_{\mathcal R}(r)}\Big\{\frac{(r-k)\,\mathcal U_{\mathcal R}-r}{D^2}-\frac{k\,(T_0+W-P)}{D}-P_r-\min\{\mathcal G,P_h\}\Big\},\quad k=h+\nu(r;x),\quad(121)$$
--   using one-sided derivatives at interpolation boundaries. If $\mathcal V(b_4,h)\ge\bar V$ for every admissible terminal state, then for every $\lambda\in\Lambda(\mathcal R)$
--   $$\bar\ell_\lambda\le\Gamma_1+T_0(0)+W(0)-P(0,0).\quad(122)$$
--
--   Differences from the source:
--   - encoding: Λ: measurable λ : [0,1] → [0,1], identified when equal a.e. → Profile: measurable functions ℝ → ℝ with values in [0,1] on [0,1]; quantifying over representatives; reason: every quantity depends only on the a.e. class on [0,1]; a measurable function on [0,1] extends measurably to ℝ
--   - generalization: (113) as a regional bound (used on [0, b4] in (120)) → (113) assumed only for r ∈ [0, b4]; reason: a weaker hypothesis; the proof uses (113) only on [0, b4], and the source's hypothesis implies it
--   - generalization: Appendix G.2 constructs G ≥ 0 such that (114) → no sign condition on G; reason: the proposition's argument ((124) and integration) does not use G ≥ 0; every G ≥ 0 is included
--   - encoding: the integral inequality (114) → (114) together with integrability of its left-hand integrand on [0, b4]; reason: an inequality between Lebesgue integrals presupposes they exist; this rules out Bochner's junk value 0
--   - encoding: sup over D_R(r) of the Bellman residual ≤ −W′(r) → for all (x, h) with Admissible R r x h, residual ≤ −deriv W r, for a.e. r ∈ [0, b4]; reason: a supremum is ≤ c iff every element is
--   - reading: 'At interpolation boundaries use the corresponding one-sided derivatives' → P_r and P_h are right derivatives (derivWithin on [r, ∞), resp. [h, ∞)) at every point; reason: r increases and h is nondecreasing along every path, so the right derivatives are the corresponding ones; off the grid lines they are the partial derivatives
--   - encoding: P continuous piecewise-bilinear on a finite grid; W absolutely continuous → IsGridBilinear P on a grid covering [0, b4] × [0, b4]; AbsolutelyContinuousOnInterval W 0 b4; reason: admissible states (r, h) on [0, b4] satisfy 0 ≤ h ≤ r ≤ b4; continuity on the grid follows from the cellwise formula
--   - reading: 'V(b4, h) ≥ V̄ for every admissible terminal state' → V̄ ≤ T0(b4) + W(b4) − P(b4, h) for every (x, h) ∈ D_R(b4); reason: the admissible states at r = b4 are those of D_R(b4)
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), Proposition F.4, p. 55

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Certificate

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-- Proposition F.4 (Regional Bellman certificate), p. 55, with regional bound `U_R`
(113), correction term `G` (114), continuation bound `V̄`, piecewise-bilinear potential `P`
and scalar potential `W`; `P_r`, `P_h` are right-sided partial derivatives. -/
theorem proposition_F_4 (R : ParamBox) (hR : R.Valid) (UR G : ℝ → (Fin 4 → ℝ) → ℝ → ℝ)
    (P : ℝ → ℝ → ℝ) (W : ℝ → ℝ) (Vbar : ℝ)
    (h113 : ∀ lam : Profile, InRegion R lam.1 → ∀ r ∈ Icc 0 (blockEnd 4),
      Rc lam.1 r + XiPlus lam.1 r ≤ UR r (massVec lam.1) (hExp lam.1 r))
    (h114 : ∀ lam : Profile, InRegion R lam.1 →
      IntegrableOn (fun r => sigmaC lam.1 r * (1 - lam.1 (uA r)) * G r (massVec lam.1) (hExp lam.1 r))
          (Icc 0 (blockEnd 4)) ∧
        ∫ r in (0 : ℝ)..blockEnd 4, sigmaC lam.1 r * (1 - lam.1 (uA r)) * G r (massVec lam.1) (hExp lam.1 r)
          ≤ ∫ r in (0 : ℝ)..blockEnd 4, sigmaC lam.1 r * (r - kRate lam.1 r) * XiPlus lam.1 r / Dc r ^ 2)
    (hV : ∀ lam : Profile, InRegion R lam.1 → contV lam.1 (blockEnd 4) ≤ Vbar)
    (hP : IsGridBilinear P 0 (blockEnd 4) 0 (blockEnd 4))
    (hW : AbsolutelyContinuousOnInterval W 0 (blockEnd 4))
    (h121 : ∀ᵐ r ∂(volume.restrict (Icc 0 (blockEnd 4))), ∀ (x : Fin 4 → ℝ) (h : ℝ),
      Admissible R r x h →
        ((r - (h + nuR r x)) * UR r x h - r) / Dc r ^ 2
            - (h + nuR r x) * (T0 r + W r - P r h) / Dc r
            - derivWithin (fun s => P s h) (Ici r) r
            - min (G r x h) (derivWithin (fun s => P r s) (Ici h) h) ≤ -deriv W r)
    (hterm : ∀ (x : Fin 4 → ℝ) (h : ℝ), Admissible R (blockEnd 4) x h →
      Vbar ≤ T0 (blockEnd 4) + W (blockEnd 4) - P (blockEnd 4) h) :
    ∀ lam : Profile, InRegion R lam.1 →
      auxLoad lam.1 ≤ ENNReal.ofReal (Gamma1 + T0 0 + W 0 - P 0 0) := by sorry

end OrderSelProphet.Kernel
