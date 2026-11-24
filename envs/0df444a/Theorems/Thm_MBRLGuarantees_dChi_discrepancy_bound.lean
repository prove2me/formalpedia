-- Prove2me | Theorems.Thm_MBRLGuarantees_dChi_discrepancy_bound
-- name    : MBRLGuarantees.dChi_discrepancy_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:42:01.661806+00:00
-- url     : https://prove2.me/theorems/c79bf565-2946-4902-9f30-26d49abbc2d3
-- title:
--   Proposition A.2 (as proved, corrected powers of $\delta$ and $\varepsilon_2$): the $\chi^2$-based discrepancy bound satisfies (R1) and (R2)
-- statement:
--   Let $\gamma\in[0,1)$, let $R$ be bounded and measurable, let $S_0\sim\mu_0$, let $M^\star$ be the true model and $\delta\ge0$. Take $d=d^{\chi^2}$ and
--
--   $$D_{\pi_{\mathrm{ref}}}(\widehat M,\pi)=(1-\gamma)^{-1}\varepsilon_1+(1-\gamma)^{-2}\,\delta^{1/2}\varepsilon_2^{1/2}+(1-\gamma)^{-5/2}\,\delta^{3/4}\varepsilon_{\max},$$
--
--   where $\varepsilon_1=\mathbb E_{S\sim\rho^{\pi_{\mathrm{ref}}}}|G^{\pi,\widehat M}(S)|$, $\varepsilon_2=\mathbb E_{S\sim\beta^{\pi_{\mathrm{ref}}}}G^{\pi,\widehat M}(S)^2$, $\varepsilon_{\max}=\sup_S|G^{\pi,\widehat M}(S)|$, all computed on $M^\star$. Then
--
--   1. (R1) for all policies $\pi,\pi_{\mathrm{ref}}$ and every model $\widehat M$ with $d^{\chi^2}(\pi,\pi_{\mathrm{ref}})\le\delta$ (and $s\mapsto\chi^2(\pi(\cdot\mid s),\pi_{\mathrm{ref}}(\cdot\mid s))$ measurable), $V^{\pi,M^\star}\ge V^{\pi,\widehat M}-D_{\pi_{\mathrm{ref}}}(\widehat M,\pi)$;
--   2. (R2) $D_{\pi_{\mathrm{ref}}}(M^\star,\pi)=0$ for all $\pi,\pi_{\mathrm{ref}}$.
--
--   **Formalization Note** The paper prints $D^{\chi^2}=(1-\gamma)^{-1}\varepsilon_1+(1-\gamma)^{-2}\delta\varepsilon_2+(1-\gamma)^{-5/2}\delta^{3/2}\varepsilon_{\max}$. Its proof in Appendix C.2 uses $\delta_1\le(1-\gamma)^{-1}\delta$, but $d^{\chi^2}\le\delta$ only gives $\delta_1\le(1-\gamma)^{-1}\delta^{1/2}$. It also writes $\delta_1\varepsilon_2$ for $\delta_1\langle\beta^{\pi_{\mathrm{ref}}},f^2\rangle^{1/2}=\delta_1\varepsilon_2^{1/2}$. Correcting both steps gives the bound above. The printed bound is false: a two-state example violates it (see the mission report). The paper's $\varepsilon_2$ uses $G(S,A)^2$ with $A$ unspecified; the statement uses $G(S)^2$, as the proof does.
-- source:
--   Luo, Xu, Li, Tian, Darrell and Ma, Algorithmic Framework for Model-based Deep Reinforcement Learning with Theoretical Guarantees, arXiv:1807.03858v5 (ICLR 2019), Appendix A, Definition A.1, eqs. (A.1)-(A.2), Proposition A.2, p. 16; proof in Appendix C.2, p. 18

import Mathlib
import Definitions.Def_MBRLGuarantees_Basic

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace MBRLGuarantees

theorem dChi_discrepancy_bound {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (R : S × A → ℝ) (hRm : Measurable R) (hRb : ∃ C, ∀ x, |R x| ≤ C)
    (μ₀ : Measure S) [IsProbabilityMeasure μ₀] (Mstar : Kernel (S × A) S) [IsMarkovKernel Mstar]
    (δ : ℝ) (hδ : 0 ≤ δ) :
    (∀ (piref pi : Kernel S A) (Mhat : Kernel (S × A) S), IsMarkovKernel piref →
      IsMarkovKernel pi → IsMarkovKernel Mhat → Measurable (fun s => chiSq (pi s) (piref s)) →
      dChi γ μ₀ Mstar pi piref ≤ ENNReal.ofReal δ →
      value γ R μ₀ pi Mhat -
          ((1 - γ)⁻¹ * epsOne γ R μ₀ Mstar piref pi Mhat +
            ((1 - γ) ^ 2)⁻¹ * Real.sqrt δ * Real.sqrt (epsTwo γ R μ₀ Mstar piref pi Mhat) +
            ((1 - γ) ^ (5 / 2 : ℝ))⁻¹ * δ ^ (3 / 4 : ℝ) * epsMax γ R Mstar pi Mhat) ≤
        value γ R μ₀ pi Mstar) ∧
    (∀ piref pi : Kernel S A, IsMarkovKernel piref → IsMarkovKernel pi →
      (1 - γ)⁻¹ * epsOne γ R μ₀ Mstar piref pi Mstar +
          ((1 - γ) ^ 2)⁻¹ * Real.sqrt δ * Real.sqrt (epsTwo γ R μ₀ Mstar piref pi Mstar) +
          ((1 - γ) ^ (5 / 2 : ℝ))⁻¹ * δ ^ (3 / 4 : ℝ) * epsMax γ R Mstar pi Mstar = 0) := by sorry

end MBRLGuarantees
