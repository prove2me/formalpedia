-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_forall_sum_coeff_mul_sqrt_zpow_mul_setIntegral_units_eq_coeff_of_mellin_mul_eval_eq_cpow_mul_eval_of_re_lt
-- name    : LanglandsTunnell.TateLocal.forall_sum_coeff_mul_sqrt_zpow_mul_setIntegral_units_eq_coeff_of_mellin_mul_eval_eq_cpow_mul_eval_of_re_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/ab1be4d2-4b34-5874-8cb9-fdd67fd8aed2
-- title:
--   Shell integrals recovered from a rational Mellin transform
-- statement:
--   Let $p$ be a nonzero prime of the ring of integers of $\mathbb{Q}$, write $F$ for the completion $\mathbb{Q}_p$ with its valuation ring $\mathcal{O}$, and set $N=\mathrm{absNorm}(p)$. Let $\varpi\in\mathcal{O}$ have nonzero image in $F$ and valuation $\exp(-1)$, i.e. be a uniformiser. Let $f\colon F^{\times}\to\mathbb{C}$ be locally constant and such that $f(y)=0$ for $\lVert y\rVert$ larger than some constant $C$. Let $P,Q\in\mathbb{C}[X]$, $m\in\mathbb{Z}$ and $\sigma_0\in\mathbb{R}$. All integrals are taken for the measure $d^{\times}y$ on $F^{\times}$ obtained by pulling back along $u\mapsto u$ the measure on $F\setminus\{0\}$ with density $\mathrm{modulus}(x)^{-1}$ against the self-dual additive Haar measure of $F$ (the additive Haar measure giving $\mathcal{O}$ mass $N^{-\ell/2}$, $\ell$ the level of the standard local additive character), $F$ carrying its Borel $\sigma$-algebra. Assume that for every $s\in\mathbb{C}$ with $\operatorname{Re} s<\sigma_0$ the function $y\mapsto f(y)\,\mathrm{modulus}(y)^{1/2-s}$ is integrable and $$\Bigl(\int_{F^{\times}}f(y)\,\mathrm{modulus}(y)^{1/2-s}\,d^{\times}y\Bigr)\,Q(N^{-s})=N^{ms}\,P(N^{-s}).$$ Then for every $k\in\mathbb{Z}$, $$\sum_{j=0}^{\deg Q}Q_j\,(\sqrt{N})^{\,k-j}\int_{\{u\,:\,v(u)=1\}}f(\varpi^{\,j-k}u)\,d^{\times}u$$ equals the coefficient of $X^{k+m}$ in $P$ when $k+m\ge 0$, and $0$ otherwise.
--
--   This is the coefficient-extraction step of Tate's local theory: the Mellin transform of $f$ is a Laurent expansion in $N^{-s}$ whose coefficients are the shell integrals $\int_{\mathcal{O}^{\times}}f(\varpi^{n}u)\,d^{\times}u$, and clearing the denominator $Q$ turns a rational identity valid on a left half-plane into these finitely many linear relations among shells. It is used in the construction of the local Rankin–Selberg integrals, both in the principal-series and in the cuspidal case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_forall_sum_coeff_mul_sqrt_zpow_mul_setIntegral_units_eq_coeff_of_mellin_mul_eval_eq_cpow_mul_eval_of_re_lt.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal
open NumberField.AdelicLevel (diagOne)

theorem LanglandsTunnell.TateLocal.forall_sum_coeff_mul_sqrt_zpow_mul_setIntegral_units_eq_coeff_of_mellin_mul_eval_eq_cpow_mul_eval_of_re_lt
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (f : (p.adicCompletion ℚ)ˣ → ℂ) (hf : IsLocallyConstant f)
    (hfsupp : ∃ C : ℝ, ∀ y : (p.adicCompletion ℚ)ˣ, C < ‖(y : (p.adicCompletion ℚ))‖ → f y = 0)
    (P Q : Polynomial ℂ) (m : ℤ) (σ₀ : ℝ)
    (hmellin : letI := localBorel ℚ p
      ∀ s : ℂ, s.re < σ₀ →
        Integrable (fun y : (p.adicCompletion ℚ)ˣ => f y * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 - s))
          (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
        (∫ y : (p.adicCompletion ℚ)ˣ, f y * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 - s)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) :
    letI := localBorel ℚ p
    ∀ k : ℤ,
      (∑ j ∈ Finset.range (Q.natDegree + 1),
          Q.coeff j * ((Real.sqrt (Ideal.absNorm p.asIdeal : ℝ) : ℝ) : ℂ) ^ (k - (j : ℤ)) *
            ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : (p.adicCompletion ℚ)) = 1},
              f ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ ((j : ℤ) - k) * u)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
        (if 0 ≤ k + m then P.coeff (k + m).toNat else 0) := by sorry
