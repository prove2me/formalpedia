-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion
-- name    : LanglandsTunnell.TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/aa5225ae-640a-533d-8523-210fd31b07d0
-- title:
--   Inversion in an additive Haar integral: d(x⁻¹)=|x|⁻² dx
-- statement:
--   Let $F$ be a number field, $v$ a nonzero prime of its ring of integers $\mathcal O_F$ (a point of the height-one spectrum), and let $F_v$ denote the $v$-adic completion of $F$, equipped with a measurable space structure which is the Borel structure of its topology. Let $\mu$ be an additive Haar measure on $F_v$ and let $f : F_v \to \mathbb{C}$ be an arbitrary function. Then the Bochner integrals of $x \mapsto f(x^{-1})$ and of $u \mapsto (\mathrm{mod}(u)^2)^{-1} \cdot f(u)$ against $\mu$ agree, where $\mathrm{mod}$ is [`LanglandsTunnell.TateLocal.modulus`](def/LanglandsTunnell_TateLocalZeta.html#L15), defined to be $0$ at $0$ and, at $a \neq 0$, the value of the distributive Haar character of $F_v$ at the unit $a$, i.e. the factor by which multiplication by $a$ scales $\mu$; the nonnegative real $\mathrm{mod}(u)^2$ is inverted in $\mathbb{R}$ (so the scalar is $0$ at $u = 0$) and acts on $f(u)$ by scalar multiplication. No measurability or integrability hypothesis on $f$ is imposed: the assertion includes the case where neither side is integrable and both integrals are $0$ by convention.
--
--   This is the Jacobian for inversion on a nonarchimedean local field, $d(x^{-1}) = |x|_v^{-2}\,d x$, equivalently the statement that $d\mu(x)/|x|_v$ is an (inversion-invariant) Haar measure on $F_v^{\times}$. It is used for the change of variables in local zeta integrals and in the Bruhat-decomposition manipulation of local intertwining integrals, and is cited in the construction of local zeta functions and their functional equations in the Langlands–Tunnell part of the development; the proof identifies the modulus of $F_v$ with the valuation norm via [`LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm`](thm.html#LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion.lean

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped NNReal

theorem LanglandsTunnell.TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (f : v.adicCompletion F → ℂ) :
    ∫ x, f x⁻¹ ∂μ
      = ∫ u, ((((LanglandsTunnell.TateLocal.modulus u : ℝ≥0) : ℝ) ^ 2)⁻¹ : ℝ) • f u ∂μ := by sorry
