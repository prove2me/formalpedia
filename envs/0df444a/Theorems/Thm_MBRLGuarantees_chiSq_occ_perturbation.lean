-- Prove2me | Theorems.Thm_MBRLGuarantees_chiSq_occ_perturbation
-- name    : MBRLGuarantees.chiSq_occ_perturbation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:36:21.810362+00:00
-- url     : https://prove2.me/theorems/98048121-909e-46e0-beb1-c9ab7af02133
-- title:
--   Lemma D.4: $\chi^2$ control of the change of a discounted state distribution
-- statement:
--   Let $\gamma\in[0,1)$, let $P,P'$ be Markov kernels on $\mathcal S$, let $\mu$ be a probability distribution, and let $\bar G=(1-\gamma)\sum_{k\ge0}\gamma^kP^k$ and $\bar G'=(1-\gamma)\sum_{k\ge0}\gamma^k{P'}^k$. Let $f$ be measurable with $|f|\le F$, assume $x\mapsto\chi^2(P'(\cdot\mid x),P(\cdot\mid x))$ is measurable, and assume $\chi^2_{\bar G\mu}(P',P)<\infty$. Put
--
--   $$\delta_1=(1-\gamma)^{-1}\chi^2_{\bar G\mu}(P',P)^{1/2},\qquad\delta_2=(1-\gamma)^{-1}\chi^2_{\bar GP\bar G\mu}(P',P)^{1/2}.$$
--
--   Then
--
--   $$\big|\langle\bar G'\mu,f\rangle-\langle\bar G\mu,f\rangle\big|\le\delta_1F$$
--
--   and
--
--   $$\big|\langle\bar G'\mu,f\rangle-\langle\bar G\mu,f\rangle\big|\le\delta_1\langle\bar GP\bar G\mu,f^2\rangle^{1/2}+\delta_1\delta_2^{1/2}F.$$
--
--   This is the perturbation bound behind the refined discrepancy bound of Proposition A.2.
--
--   **Formalization Note** The sup norm $\|f\|_\infty$ is replaced by an arbitrary bound $F$ on $|f|$, which is equivalent. The paper's $\delta_1,\delta_2$ are real numbers, so its statement presupposes $\chi^2_{\bar G\mu}(P',P)<\infty$; this is the hypothesis `hfin`. Without it the $[0,\infty]$-valued second bound would be false because $\infty\cdot0=0$ in $[0,\infty]$: on two states with $\mu=\delta_0$, $P\equiv\delta_1$, $P'(0)=\delta_0$, $P'(1)=\delta_1$, $f=\mathbf 1_{\{0\}}$, $\gamma=0.3$, one has $\chi^2_{\bar G\mu}=\infty$ and $\chi^2_{\bar GP\bar G\mu}=0$, so the right side would be $\infty\cdot0+\infty\cdot0=0$ while the left side is $0.3$. With `hfin`, an infinite $\delta_2$ makes the right side $\infty$ (or the left side $0$), so the $[0,\infty]$ encoding is harmless.
-- source:
--   Luo, Xu, Li, Tian, Darrell and Ma, Algorithmic Framework for Model-based Deep Reinforcement Learning with Theoretical Guarantees, arXiv:1807.03858v5 (ICLR 2019), Appendix D.1, Lemma D.4, p. 20 (eq. (D.1) and Definition E.3)

import Mathlib
import Definitions.Def_MBRLGuarantees_Basic

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace MBRLGuarantees

theorem chiSq_occ_perturbation {S : Type*} [MeasurableSpace S]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (P P' : Kernel S S) [IsMarkovKernel P] [IsMarkovKernel P']
    (μ : Measure S) [IsProbabilityMeasure μ] (f : S → ℝ) (hf : Measurable f) (F : ℝ)
    (hF : ∀ x, |f x| ≤ F) (hchi : Measurable fun x => chiSq (P' x) (P x))
    (hfin : chiSqTrans (discOcc γ P μ) P' P ≠ ∞) :
    let d1 := ENNReal.ofReal (1 - γ)⁻¹ * chiSqTrans (discOcc γ P μ) P' P ^ (1 / 2 : ℝ)
    let d2 := ENNReal.ofReal (1 - γ)⁻¹ *
      chiSqTrans (discOcc γ P ((discOcc γ P μ).bind P)) P' P ^ (1 / 2 : ℝ)
    ENNReal.ofReal |(∫ x, f x ∂(discOcc γ P' μ)) - ∫ x, f x ∂(discOcc γ P μ)| ≤
        d1 * ENNReal.ofReal F ∧
      ENNReal.ofReal |(∫ x, f x ∂(discOcc γ P' μ)) - ∫ x, f x ∂(discOcc γ P μ)| ≤
        d1 * (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂(discOcc γ P ((discOcc γ P μ).bind P))) ^ (1 / 2 : ℝ) +
          d1 * d2 ^ (1 / 2 : ℝ) * ENNReal.ofReal F := by sorry

end MBRLGuarantees
