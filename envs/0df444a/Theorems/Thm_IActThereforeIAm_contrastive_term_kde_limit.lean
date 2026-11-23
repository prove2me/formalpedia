-- Prove2me | Theorems.Thm_IActThereforeIAm_contrastive_term_kde_limit
-- name    : IActThereforeIAm.contrastive_term_kde_limit
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:09:15.423282+00:00
-- url     : https://prove2.me/theorems/ea676cc0-1e76-47e2-8be4-fdca11a6e036
-- title:
--   Proposition E.1, Eq. (59): the contrastive term tends to a log kernel-density value
-- statement:
--   Let $\sigma,\tau>0$, let $d\ge0$, and set $b=\sqrt{\tau\sigma^2}$. There is a constant $C_{\sigma,\tau}$ with the following property. Take any probability law $p_{\mathbf z}$ on $\mathbb R^d$, i.i.d. samples $\mathbf z^{(1)},\mathbf z^{(2)},\dots$ from $p_{\mathbf z}$, and any $\mathbf z_t\in\mathbb R^d$, and let the prediction be locally accurate, $\boldsymbol\mu_\phi(\mathbf z_{t-1},\mathbf a_{t-1})=\mathbf z_t$. Then almost surely
--
--   $$U_K=\log\Big[\frac1K\sum_{k=1}^K\exp\Big(-\frac{\ell_\phi(\mathbf z^{(k)}\mid\mathbf z_{t-1},\mathbf a_{t-1})}{\tau}\Big)\Big]\longrightarrow\log\big[(p_{\mathbf z}*\varphi_b)(\mathbf z_t)\big]+C_{\sigma,\tau}\qquad(K\to\infty).$$
--
--   Here $\ell_\phi$ is the negative log-likelihood of $\mathcal N(\mathbf z_t,\sigma^2I)$ and $\varphi_b$ the Gaussian kernel of bandwidth $b$.
--
--   This relates the contrastive term of A-JEPA to a Gaussian kernel-density estimate of the representation law.
--
--   **Formalization Note** Only Eq. (59) is stated. Its convergence mode is taken as almost sure for each fixed $\mathbf z_t$, as the law-of-large-numbers proof gives. "Independent of the representation distribution" is encoded by choosing $C$ before $p_{\mathbf z}$. The samples are a mutually independent sequence. Eqs. (60) and (62) are not included.
-- source:
--   Liu, Huang and Shi, I Act Therefore I Am: When Is JEPA's Action-Conditioning Enough to Learn Causal Mechanisms?, arXiv:2609.31161v1 (2026), Appendix E, Proposition E.1, Eqs. (56)-(59), p. 22

import Mathlib
import Definitions.Def_IActThereforeIAm_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace IActThereforeIAm

theorem contrastive_term_kde_limit {d : ℕ} (σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (Zs : ℕ → Ω → Fin d → ℝ),
      (∀ k, Measurable (Zs k)) → ProbabilityTheory.iIndepFun Zs P → (∀ k, P.map (Zs k) = μ) →
      ∀ zt : Fin d → ℝ, ∀ᵐ w ∂P,
        Tendsto (fun K => contrastiveU σ τ zt (fun k => Zs k w) K) atTop
          (𝓝 (Real.log (kernelSmoothed μ (Real.sqrt (τ * σ ^ 2)) zt) + C)) := by sorry

end IActThereforeIAm
