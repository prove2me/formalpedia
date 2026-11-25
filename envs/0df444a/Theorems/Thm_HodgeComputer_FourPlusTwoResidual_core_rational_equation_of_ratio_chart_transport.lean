-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_core_rational_equation_of_ratio_chart_transport
-- name    : HodgeComputer.FourPlusTwoResidual.core_rational_equation_of_ratio_chart_transport
-- status  : Open
-- author  : @pageman
-- created : 2026-11-25T14:15:24.116445+00:00
-- url     : https://prove2.me/theorems/3bae0eb2-4815-4ca9-9bf9-d465db2bc93e
-- title:
--   Ratio-chart transport yields `CoreRationalEquation` under $\delta$-frame matching
-- statement:
--   **Claim.** Let $K$ be a field of fractions of $R=\mathbb{C}[x_0,x_1,y_0,y_1]$ with coordinate derivations $\delta_i$ extending $\partial_i$. Suppose $(D_r,D_s,D_t,a,s,t,P,q_r,q_s,q_t)$ is a `RatioChartT4Witness` with homogenization
--   $$
--   a^6\cdot P=\iota(H),\qquad a^6\cdot t^3=\iota(x_0^3 y_0^3),
--   $$
--   and with $\delta$-frame matching
--   $$
--   \delta_1=\frac{D_r}{a},\qquad
--   \delta_2=\frac{D_t-(s/t)D_s}{a},\qquad
--   \delta_3=\frac{D_s}{a\cdot t}.
--   $$
--   Then there exists a rational vector field $v\colon\mathrm{Fin}\,4\to K$ satisfying `CoreRationalEquation` for $\delta$.
--
--   **Proof idea.** Apply the proved identity `ratioChart_transport` to obtain
--   $$
--   p_b\,\partial_b H+p_c\,\partial_c H+p_d\,\partial_d H-\tfrac32 H\,(\partial_b p_b+\partial_c p_c+\partial_d p_d)=a^6 t^3
--   $$
--   for the transported components $(p_a,p_b,p_c,p_d)=(0,p_b,p_c,p_d)$ built from $(q_r,q_s,q_t)$ by the standard scaling. Frame matching identifies the chart directional operators with $\delta_1,\delta_2,\delta_3$, and the homogenization hypotheses rewrite the right-hand side as $\iota(x_0^3 y_0^3)$ and the potential as $\iota(H)$, which is exactly `CoreRationalEquation` for $v=(0,p_b,p_c,p_d)$.
-- source:
--   HodgeComputer four-plus-two residual; WORMHOLE Epoch-4 child of exists_core_rational_vector_field (0868e494); uses proved ratioChart_transport

import Definitions.Def_HodgeComputerFourPlusTwoWormholeBridge
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Derivation.Basic

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual
open MvPolynomial

theorem HodgeComputer.FourPlusTwoResidual.core_rational_equation_of_ratio_chart_transport
    {K : Type} [Field K] [CharZero K]
    [Algebra (MvPolynomial (Fin 4) ℂ) K]
    [IsFractionRing (MvPolynomial (Fin 4) ℂ) K]
    (δ : Fin 4 → Derivation ℤ K K)
    (hδ : ∀ (i : Fin 4) (p : MvPolynomial (Fin 4) ℂ),
      δ i (algebraMap (MvPolynomial (Fin 4) ℂ) K p) =
        algebraMap (MvPolynomial (Fin 4) ℂ) K (MvPolynomial.pderiv i p))
    (Dr Ds Dt : Derivation ℤ K K)
    (a s t P qr qs qt : K)
    (hW : RatioChartT4Witness Dr Ds Dt a s t P qr qs qt)
    (hP : a ^ 6 * P = algebraMap (MvPolynomial (Fin 4) ℂ) K core)
    (hSrc : a ^ 6 * t ^ 3 = algebraMap (MvPolynomial (Fin 4) ℂ) K coreSource)
    (hFrame1 : ∀ z : K, δ 1 z = Dr z / a)
    (hFrame2 : ∀ z : K, δ 2 z = (Dt z - s / t * Ds z) / a)
    (hFrame3 : ∀ z : K, δ 3 z = Ds z / (a * t)) :
    ∃ v : Fin 4 → K, CoreRationalEquation δ v := by sorry
