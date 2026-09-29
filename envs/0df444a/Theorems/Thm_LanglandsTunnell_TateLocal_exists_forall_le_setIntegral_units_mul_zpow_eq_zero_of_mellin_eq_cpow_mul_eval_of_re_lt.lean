-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_exists_forall_le_setIntegral_units_mul_zpow_eq_zero_of_mellin_eq_cpow_mul_eval_of_re_lt
-- name    : LanglandsTunnell.TateLocal.exists_forall_le_setIntegral_units_mul_zpow_eq_zero_of_mellin_eq_cpow_mul_eval_of_re_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/6f1cefee-4d52-5a9a-a505-723c0766b540
-- title:
--   Vanishing of deep shell integrals from a Laurent-polynomial Mellin transform
-- statement:
--   Let $p$ be a nonzero prime ideal of the ring of integers of $\mathbb{Q}$, and let $\varpi$ be an element of the valuation ring of the completion $\mathbb{Q}_p$ at $p$ whose image in $\mathbb{Q}_p$ is nonzero and has valuation $\exp(-1)$, i.e. a uniformiser. Let $f\colon \mathbb{Q}_p^\times\to\mathbb{C}$ be locally constant and assume there is a real $C$ with $f(y)=0$ whenever $\|y\|>C$. Let $P$ be a polynomial over $\mathbb{C}$, $m$ an integer and $\sigma_0$ a real number. The measure used throughout is the pullback along $y\mapsto y$ of $\mathbb{Q}_p^\times\hookrightarrow\mathbb{Q}_p$ of the multiplicative measure attached to `selfDualHaarAt`, that is, of the measure on $\mathbb{Q}_p\setminus\{0\}$ with density $\mathrm{modulus}(x)^{-1}$ against the additive Haar measure normalised to give the ring of integers measure $1$ and then scaled by $N(p)^{-\ell/2}$, where $\ell$ is the level of the local standard additive character $\psi_p$ (the supremum of the integers $n$ with $\psi_p$ trivial on $\{\mathrm{v}(x)\le\exp(n)\}$), and where $\mathrm{modulus}(x)$ is the module of $x$, i.e. the scaling factor of additive Haar measure under multiplication by $x$ (and $0$ for $x=0$). The hypothesis is that for every $s$ with $\operatorname{Re} s<\sigma_0$ the function $y\mapsto f(y)\,\mathrm{modulus}(y)^{1/2-s}$ is integrable for this measure and $$\int_{\mathbb{Q}_p^\times} f(y)\,\mathrm{modulus}(y)^{1/2-s}\,d^\times y \;=\; N(p)^{ms}\,P\bigl(N(p)^{-s}\bigr),$$ with $N(p)$ the absolute norm of $p$. Note that the half-plane of validity is a left half-plane. The conclusion is that there exists an integer $n_0$ such that for every $n\ge n_0$ the shell integral $\int_{\{u:\ \mathrm{v}(u)=1\}} f(\varpi^{n}u)\,d^\times u$ vanishes.
--
--   This is the local Mellin-inversion step in Tate's local theory: expanding the multiplicative integral over the shells $\varpi^n\mathcal{O}^\times$ turns the Mellin transform into a Laurent series in $N(p)^{s}$, so a Laurent-polynomial value forces all sufficiently deep shell integrals to vanish. It is used in the Rankin–Selberg part of the development, in the statement [`LanglandsTunnell.RankinSelberg.exists_forall_le_setIntegral_localLevelOne_dualJacquet_mul_partner_mul_eq_zero_of_dualTorusZeta_polynomial`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_le_setIntegral_localLevelOne_dualJacquet_mul_partner_mul_eq_zero_of_dualTorusZeta_polynomial), to control Kirillov-type local integrals attached to a torus zeta integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_exists_forall_le_setIntegral_units_mul_zpow_eq_zero_of_mellin_eq_cpow_mul_eval_of_re_lt.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal
open NumberField.AdelicLevel (diagOne)

theorem LanglandsTunnell.TateLocal.exists_forall_le_setIntegral_units_mul_zpow_eq_zero_of_mellin_eq_cpow_mul_eval_of_re_lt
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (f : (p.adicCompletion ℚ)ˣ → ℂ) (hf : IsLocallyConstant f)
    (hfsupp : ∃ C : ℝ, ∀ y : (p.adicCompletion ℚ)ˣ, C < ‖(y : (p.adicCompletion ℚ))‖ → f y = 0)
    (P : Polynomial ℂ) (m : ℤ) (σ₀ : ℝ)
    (hmellin : letI := localBorel ℚ p
      ∀ s : ℂ, s.re < σ₀ →
        Integrable (fun y : (p.adicCompletion ℚ)ˣ => f y * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 - s))
          (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
        ∫ y : (p.adicCompletion ℚ)ˣ, f y * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 - s)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) =
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) :
    letI := localBorel ℚ p
    ∃ n0 : ℤ, ∀ n : ℤ, n0 ≤ n →
      ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : (p.adicCompletion ℚ)) = 1},
          f ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n * u)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) = 0 := by sorry
