-- Prove2me | Theorems.Thm_MBRLGuarantees_dKL_discG_satisfies_requirements
-- name    : MBRLGuarantees.dKL_discG_satisfies_requirements
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:32:31.374038+00:00
-- url     : https://prove2.me/theorems/60e1330a-6cd7-488c-b1bd-915c5f940492
-- title:
--   Proposition 4.4: $d^{KL}$ and $D^G$ satisfy (R1) and (R2)
-- statement:
--   Let $\gamma\in[0,1)$, let $R$ be bounded and measurable, let $S_0\sim\mu_0$, let $M^\star$ be the true model and $\delta\ge0$. With $d=d^{\mathrm{KL}}$ and
--
--   $$D^G_{\pi_{\mathrm{ref}},\delta}(\widehat M,\pi)=\kappa\,\varepsilon_1+\kappa^2\delta\,\varepsilon_{\max},\qquad\varepsilon_1=\mathbb E_{S\sim\rho^{\pi_{\mathrm{ref}}}}|G^{\pi,\widehat M}(S)|,\quad\varepsilon_{\max}=\sup_S|G^{\pi,\widehat M}(S)|,$$
--
--   1. (R1) for all policies $\pi,\pi_{\mathrm{ref}}$ and every model $\widehat M$ with $d^{\mathrm{KL}}(\pi,\pi_{\mathrm{ref}})\le\delta$ (and $s\mapsto\mathrm{KL}(\pi(\cdot\mid s),\pi_{\mathrm{ref}}(\cdot\mid s))$ measurable), $V^{\pi,M^\star}\ge V^{\pi,\widehat M}-D^G_{\pi_{\mathrm{ref}},\delta}(\widehat M,\pi)$;
--   2. (R2) $D^G_{\pi_{\mathrm{ref}},\delta}(M^\star,\pi)=0$ for all $\pi,\pi_{\mathrm{ref}}$.
--
--   Here $G^{\pi,\widehat M}$ is computed against $M^\star$ and $\rho^{\pi_{\mathrm{ref}}}$ is taken on $M^\star$.
--
--   **Formalization Note** The paper writes $\varepsilon_1$ with $|G^{\pi,\widehat M}(S,A)|$ and leaves $A$ unspecified; the statement uses $|G^{\pi,\widehat M}(S)|$, the quantity of the proof in Appendix C.1. Models and policies are general Markov kernels. The invariance claim of the proposition is a separate statement.
-- source:
--   Luo, Xu, Li, Tian, Darrell and Ma, Algorithmic Framework for Model-based Deep Reinforcement Learning with Theoretical Guarantees, arXiv:1807.03858v5 (ICLR 2019), Section 4.2, Proposition 4.4, eqs. (4.3), (4.7), (R1), (R2), p. 7; proof in Appendix C.1, p. 17

import Mathlib
import Definitions.Def_MBRLGuarantees_Basic

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace MBRLGuarantees

theorem dKL_discG_satisfies_requirements {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (R : S × A → ℝ) (hRm : Measurable R) (hRb : ∃ C, ∀ x, |R x| ≤ C)
    (μ₀ : Measure S) [IsProbabilityMeasure μ₀] (Mstar : Kernel (S × A) S) [IsMarkovKernel Mstar]
    (δ : ℝ) (hδ : 0 ≤ δ) :
    (∀ (piref pi : Kernel S A) (Mhat : Kernel (S × A) S), IsMarkovKernel piref →
      IsMarkovKernel pi → IsMarkovKernel Mhat → Measurable (fun s => klDiv (pi s) (piref s)) →
      dKL γ μ₀ Mstar pi piref ≤ ENNReal.ofReal δ →
      value γ R μ₀ pi Mhat - discG γ R μ₀ Mstar δ piref Mhat pi ≤ value γ R μ₀ pi Mstar) ∧
    (∀ piref pi : Kernel S A, IsMarkovKernel piref → IsMarkovKernel pi →
      discG γ R μ₀ Mstar δ piref Mstar pi = 0) := by sorry

end MBRLGuarantees
