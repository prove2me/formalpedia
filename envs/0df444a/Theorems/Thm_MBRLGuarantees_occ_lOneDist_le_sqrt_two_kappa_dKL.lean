-- Prove2me | Theorems.Thm_MBRLGuarantees_occ_lOneDist_le_sqrt_two_kappa_dKL
-- name    : MBRLGuarantees.occ_lOneDist_le_sqrt_two_kappa_dKL
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:26:31.228565+00:00
-- url     : https://prove2.me/theorems/b333b23f-4445-4a59-92d6-0543d8efdb7b
-- title:
--   Corollary E.7 (as proved, with Pinsker's constant): discounted state distributions of nearby policies
-- statement:
--   Let $\gamma\in[0,1)$, $S_0\sim\mu_0$, let $M$ be a dynamical model and $\pi,\pi'$ two policies with $s\mapsto\mathrm{KL}(\pi(\cdot\mid s),\pi'(\cdot\mid s))$ measurable. Then the discounted state distributions of $\pi$ and $\pi'$ on $M$ satisfy
--
--   $$|\rho^{\pi}-\rho^{\pi'}|_1\le\sqrt2\,\frac{\gamma}{1-\gamma}\,\mathbb E_{S\sim\rho^{\pi}}\Big[\mathrm{KL}\big(\pi(\cdot\mid S),\pi'(\cdot\mid S)\big)^{1/2}\Big]=\sqrt2\,\kappa\,d^{\mathrm{KL}}(\pi,\pi').$$
--
--   This is the step that lets the bounds of Section 4 replace the state distribution of $\pi$ by that of a nearby reference policy.
--
--   **Formalization Note** The paper prints the bound without the factor $\sqrt2$. Its proof applies Pinsker's inequality as $|p-q|_1\le\mathrm{KL}(p,q)^{1/2}$, but Pinsker's inequality is $|p-q|_1\le\sqrt{2\,\mathrm{KL}(p,q)}$, and the printed bound fails for two states with $\gamma=0.1$ (see the mission report). The model $M$ is arbitrary; the paper uses $M^\star$.
-- source:
--   Luo, Xu, Li, Tian, Darrell and Ma, Algorithmic Framework for Model-based Deep Reinforcement Learning with Theoretical Guarantees, arXiv:1807.03858v5 (ICLR 2019), Appendix E, Corollary E.7, p. 23 (with Claim E.6, p. 23)

import Mathlib
import Definitions.Def_MBRLGuarantees_Basic

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace MBRLGuarantees

theorem occ_lOneDist_le_sqrt_two_kappa_dKL {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ₀ : Measure S) [IsProbabilityMeasure μ₀]
    (M : Kernel (S × A) S) [IsMarkovKernel M] (pi pi' : Kernel S A) [IsMarkovKernel pi]
    [IsMarkovKernel pi'] (hKL : Measurable fun s => klDiv (pi s) (pi' s)) :
    lOneDist (occ γ μ₀ pi M) (occ γ μ₀ pi' M) ≤
      ENNReal.ofReal (Real.sqrt 2 * kappa γ) * dKL γ μ₀ M pi pi' := by sorry

end MBRLGuarantees
