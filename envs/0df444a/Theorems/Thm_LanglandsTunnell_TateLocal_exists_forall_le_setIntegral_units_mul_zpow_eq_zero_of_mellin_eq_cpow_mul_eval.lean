-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_exists_forall_le_setIntegral_units_mul_zpow_eq_zero_of_mellin_eq_cpow_mul_eval
-- name    : LanglandsTunnell.TateLocal.exists_forall_le_setIntegral_units_mul_zpow_eq_zero_of_mellin_eq_cpow_mul_eval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/8bf96c4c-637e-59c0-9ca2-1e9b63afac93
-- title:
--   Deep unit-shell integrals vanish when the Mellin transform is polynomial
-- statement:
--   Let $p$ be a nonzero prime of the ring of integers of $\mathbb{Q}$, write $F = \mathbb{Q}_p$ for the $p$-adic completion and $N = \#(\mathcal{O}/p)$ for the absolute norm of $p$. Let $\varpi$ lie in the valuation ring of $F$, with nonzero image in $F$ and with $v(\varpi) = \exp(-1)$, so that $\varpi$ is a uniformiser. Let $f \colon F^\times \to \mathbb{C}$ be locally constant and suppose there is $C \in \mathbb{R}$ with $f(y) = 0$ whenever $\|y\| > C$. Let $P$ be a complex polynomial, $m$ an integer and $\sigma_0$ real. All integrals are taken with respect to the measure on $F^\times$ obtained by pulling back along $u \mapsto u$ the measure $\mathrm{mulMeasure}$ of the self-dual additive Haar measure of $F$ (the additive Haar measure giving the valuation ring mass $N^{-\mathrm{addCharLevel}(\psi_p)/2}$, restricted to $F \setminus \{0\}$ and given density $|y|^{-1}$, where $|y| = \mathrm{distribHaarChar}$ of $y$), the Borel $\sigma$-algebra being used on $F$. Assume that for every $s$ with $\operatorname{Re} s > \sigma_0$ the function $y \mapsto f(y)\,|y|^{\,s-1/2}$ is integrable and $\int_{F^\times} f(y)\,|y|^{\,s-1/2}\,d^\times y = N^{ms}\,P(N^{-s})$. Then there is $n_0 \in \mathbb{Z}$ such that for all $n \ge n_0$ one has $\int_{\{u \,:\, v(u) = 1\}} f(\varpi^{n} u)\,d^\times u = 0$, the power $\varpi^{n}$ being taken in $F^\times$.
--
--   This is the coefficient-extraction step in Tate's local theory: decomposing $F^\times$ into the shells $\varpi^n \mathcal{O}^\times$ turns the local Mellin transform of $f$ into a Laurent series in $N^{-s}$ whose coefficients are the unit-shell integrals, so a Laurent-polynomial Mellin transform forces those integrals to vanish for all sufficiently deep shells. It is used in the Rankin–Selberg part of the development, where the shell integrals of a Whittaker-type function twisted along the diagonal torus are shown to vanish beyond a bound.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_exists_forall_le_setIntegral_units_mul_zpow_eq_zero_of_mellin_eq_cpow_mul_eval.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal
open NumberField.AdelicLevel (diagOne)

theorem LanglandsTunnell.TateLocal.exists_forall_le_setIntegral_units_mul_zpow_eq_zero_of_mellin_eq_cpow_mul_eval
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (f : (p.adicCompletion ℚ)ˣ → ℂ) (hf : IsLocallyConstant f)
    (hfsupp : ∃ C : ℝ, ∀ y : (p.adicCompletion ℚ)ˣ, C < ‖(y : (p.adicCompletion ℚ))‖ → f y = 0)
    (P : Polynomial ℂ) (m : ℤ) (σ₀ : ℝ)
    (hmellin : letI := localBorel ℚ p
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun y : (p.adicCompletion ℚ)ˣ => f y * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
          (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
        ∫ y : (p.adicCompletion ℚ)ˣ, f y * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) =
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) :
    letI := localBorel ℚ p
    ∃ n0 : ℤ, ∀ n : ℤ, n0 ≤ n →
      ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : (p.adicCompletion ℚ)) = 1},
          f ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n * u)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) = 0 := by sorry
