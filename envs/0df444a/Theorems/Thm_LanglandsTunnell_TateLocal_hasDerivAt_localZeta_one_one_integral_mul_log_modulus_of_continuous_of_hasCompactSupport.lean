-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_hasDerivAt_localZeta_one_one_integral_mul_log_modulus_of_continuous_of_hasCompactSupport
-- name    : LanglandsTunnell.TateLocal.hasDerivAt_localZeta_one_one_integral_mul_log_modulus_of_continuous_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/b43fc06a-6965-5dfb-927b-f76a335e2d5d
-- title:
--   Derivative at s=1 of Tate's local zeta integral
-- statement:
--   Let $K$ be a number field, let $v$ be a nonzero prime of the ring of integers $\mathcal{O}_K$, and equip the completion $K_v$ with a Borel measurable structure and an additive Haar measure $\mu$. Let $F : K_v \to \mathbb{C}$ be continuous with compact support. The function considered is $s \mapsto Z(F,\mathbf 1,s)$, where for a character $\chi$ the local zeta integral is $\int F(x)\,\chi^{\mathrm{ext}}(x)\,\|x\|^{s}\,d(\mu^{\times})(x)$; here $\|x\|$ is the module of $x$, defined as $0$ for $x = 0$ and otherwise as the value of the distributive Haar character of $K_v$ at the unit $x$ (for the adic completion this is the normalised absolute value $\|x\|_v$), $\chi^{\mathrm{ext}}$ extends $\chi$ by $0$ at the origin, $\mathbf 1$ is the trivial homomorphism $K_v^{\times} \to \mathbb{C}^{\times}$, and $\mu^{\times}$ is the multiplicative measure obtained by restricting $\mu$ to $K_v \smallsetminus \{0\}$ and taking the density $\|x\|^{-1}$. The assertion is that this function of $s \in \mathbb{C}$ is differentiable at $s = 1$ with derivative $\int F(x)\,\log\|x\|\,d\mu(x)$, the logarithm being Lean's, so that the value at $x = 0$ is $0$.
--
--   This is the first-order behaviour at the centre $s = 1$ of Tate's local zeta integral against the trivial character, for a continuous compactly supported test function at a finite place. It is used in the computation of the weighted moments occurring in the twisted unipotent terms, via [`TwistedUnipotentTerm.exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram`](thm.html#TwistedUnipotentTerm.exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_hasDerivAt_localZeta_one_one_integral_mul_log_modulus_of_continuous_of_hasCompactSupport.lean

import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_Completion_Finite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem LanglandsTunnell.TateLocal.hasDerivAt_localZeta_one_one_integral_mul_log_modulus_of_continuous_of_hasCompactSupport
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (F : v.adicCompletion K → ℂ) (hF : Continuous F) (hFc : HasCompactSupport F) :
    HasDerivAt (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta μ F 1 s)
      (∫ x, F x * ((Real.log (LanglandsTunnell.TateLocal.modulus x : ℝ) : ℝ) : ℂ) ∂μ) 1 := by sorry
