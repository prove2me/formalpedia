-- Prove2me | Theorems.Thm_InvestCommonGood_MixedTSSPE_eq_B_20
-- name    : InvestCommonGood.MixedTSSPE.eq_B_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:29.909136+00:00
-- url     : https://prove2.me/theorems/9f49e33d-d84f-4543-851e-d108598b2ebe
-- title:
--   (B.20), proof of Lemma 2, EC p. 21 — I′(x) = 2S′(x)L(x)/(σ²(x)φ′(x)²)
-- statement:
--   Let the standing assumptions and Assumptions 1, 2 and 4 hold. Then for every $x\in\mathcal I$ the derivative of $I(x)=((R_r\pi)'(x)-k)/\varphi'(x)$ is
--   $$I'(x)=\frac{2S'(x)}{\sigma^2(x)[\varphi'(x)]^2}\,L(x),$$
--   where $S'(x)=\exp[-\int_{x_0}^x2\mu/\sigma^2]$ is the scale density and $L(x)=-\rho(x)\varphi'(x)/S'(x)-r\int_x^b\varphi\rho m'$ with $\rho(x)=\pi(x)+k[\mu(x)-rx]$.
--
--   Since the prefactor is positive, $I'$ has the sign of $L$; this identity, derived from the resolvent representation (B.19), is how the proof of Lemma 2 reads off the monotonicity of $I$ from that of $L$.
-- source:
--   Kim & Kwon, Investment in the common good: free rider effect and the stability of mixed strategy equilibria, arXiv:2208.11217v1, proof of Lemma 2, EC p. 21 (PDF 52), (B.20)

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE

namespace InvestCommonGood.MixedTSSPE

theorem eq_B_20 {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (zs xs : ℝ)
    (hS : Standing m S) (hA1 : Assumption1 m S) (hA2 : Assumption2 m S zs)
    (hA4 : Assumption4 m S xs) :
    ∀ x ∈ m.I, deriv (Ifun m S) x =
      2 * Sp m x / (m.σ x ^ 2 * deriv S.φ x ^ 2) * Lfun m S x := by sorry

end InvestCommonGood.MixedTSSPE
