-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_forall_sum_coeff_mul_sqrt_zpow_mul_setIntegral_units_eq_coeff_of_mellin_mul_eval_eq_cpow_mul_eval
-- name    : LanglandsTunnell.TateLocal.forall_sum_coeff_mul_sqrt_zpow_mul_setIntegral_units_eq_coeff_of_mellin_mul_eval_eq_cpow_mul_eval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/333f03e0-8b83-588e-a280-a73eb514f394
-- title:
--   Unit-shell integrals from a rational local Mellin transform
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, and let $\varpi$ lie in the valuation ring of the completion $\mathbb{Q}_p$ at $p$, with nonzero image in $\mathbb{Q}_p$ and with valuation $\exp(-1)$, i.e. a uniformiser. Let $f\colon \mathbb{Q}_p^{\times}\to\mathbb{C}$ be locally constant and such that for some real $C$ one has $f(y)=0$ whenever $\|y\|>C$. Let $P,Q$ be polynomials over $\mathbb{C}$, $m$ an integer and $\sigma_0$ a real number. Throughout, $\mathbb{Q}_p$ carries its Borel $\sigma$-algebra, and $\mathbb{Q}_p^{\times}$ the measure obtained by pulling back along $u\mapsto u$ the measure `mulMeasure (selfDualHaarAt ℚ p)`, i.e. the restriction of the additive Haar measure normalised by the factor $(\#(\mathcal{O}/p))^{-\mathrm{level}(\psi_p)/2}$ giving the integers measure $1$ to the complement of $\{0\}$, weighted by the density $x\mapsto \mathrm{modulus}(x)^{-1}$ (here $\mathrm{modulus}$ is the module character, $0$ at $0$). Assume that for every $s$ with $\operatorname{Re} s>\sigma_0$ the function $y\mapsto f(y)\,\mathrm{modulus}(y)^{s-1/2}$ is integrable for that measure and
--   $$\Bigl(\int_{\mathbb{Q}_p^{\times}} f(y)\,\mathrm{modulus}(y)^{s-1/2}\Bigr)\cdot Q\bigl(N^{-s}\bigr)=N^{ms}\,P\bigl(N^{-s}\bigr),\qquad N=\#(\mathcal{O}/p)=\mathrm{absNorm}\,p.$$
--   Then for every integer $k$,
--   $$\sum_{j=0}^{\deg Q} Q_j\,\bigl(\sqrt{N}\bigr)^{\,k-j}\int_{\{u\,:\,v(u)=1\}} f\bigl(\varpi^{\,k-j}u\bigr) = \begin{cases} P_{k+m} & 0\le k+m,\\ 0 & \text{otherwise},\end{cases}$$
--   the sum being over $j$ in the range $0,\dots,\deg Q$, the integral over the units of the valuation ring, and $P_i$ the $i$-th coefficient of $P$.
--
--   This is the coefficient-by-coefficient form of Tate's local functional-equation bookkeeping: the unit-shell integrals $J_n=\int_{\mathcal{O}^\times} f(\varpi^n u)$ of a locally constant, boundedly supported function are recovered from a rational expression $N^{ms}P(N^{-s})/Q(N^{-s})$ for its local Mellin transform, the polynomial $Q$ playing the role of a local $L$-factor denominator. It is used in the Rankin–Selberg computations of local integrals attached to principal series and to cuspidal data, where the torus zeta integrals are cleared of their local factors and compared with Laurent data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_forall_sum_coeff_mul_sqrt_zpow_mul_setIntegral_units_eq_coeff_of_mellin_mul_eval_eq_cpow_mul_eval.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal
open NumberField.AdelicLevel (diagOne)

theorem LanglandsTunnell.TateLocal.forall_sum_coeff_mul_sqrt_zpow_mul_setIntegral_units_eq_coeff_of_mellin_mul_eval_eq_cpow_mul_eval
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (f : (p.adicCompletion ℚ)ˣ → ℂ) (hf : IsLocallyConstant f)
    (hfsupp : ∃ C : ℝ, ∀ y : (p.adicCompletion ℚ)ˣ, C < ‖(y : (p.adicCompletion ℚ))‖ → f y = 0)
    (P Q : Polynomial ℂ) (m : ℤ) (σ₀ : ℝ)
    (hmellin : letI := localBorel ℚ p
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun y : (p.adicCompletion ℚ)ˣ => f y * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
          (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
        (∫ y : (p.adicCompletion ℚ)ˣ, f y * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) :
    letI := localBorel ℚ p
    ∀ k : ℤ,
      (∑ j ∈ Finset.range (Q.natDegree + 1),
          Q.coeff j * ((Real.sqrt (Ideal.absNorm p.asIdeal : ℝ) : ℝ) : ℂ) ^ (k - (j : ℤ)) *
            ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : (p.adicCompletion ℚ)) = 1},
              f ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ (k - (j : ℤ)) * u)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
        (if 0 ≤ k + m then P.coeff (k + m).toNat else 0) := by sorry
