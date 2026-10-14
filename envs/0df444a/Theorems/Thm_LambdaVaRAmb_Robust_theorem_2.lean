-- Prove2me | Theorems.Thm_LambdaVaRAmb_Robust_theorem_2
-- name    : LambdaVaRAmb.Robust.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:38.369428+00:00
-- url     : https://prove2.me/theorems/806cf95c-fbfc-455e-a834-30337f8ee598
-- title:
--   Theorem 2 — for increasing Λ, sup over the φ-divergence ball of ΛVaR^ℚ is ΛVaR^{g_{φ,δ}∘ℙ}; strictly convex φ: (g⁻¹∘Λ)VaR^ℙ, and the δ ↓ 0 limit is ΛVaR^{+,ℙ}
-- statement:
--   Let $\mathbb P$ be a probability measure on $(\Omega,\mathcal F)$ and let $\phi:[0,\infty)\to\mathbb R\cup\{\infty\}$ be convex with $\phi(1)=0$ and $\phi(0)=\lim_{x\downarrow0}\phi(x)$. For $\delta>0$ let $\mathcal P_\phi(\mathbb P,\delta)=\{\mathbb Q\ll\mathbb P: D_\phi(\mathbb Q\|\mathbb P)\le\delta\}$ be the $\phi$-divergence ball of probability measures around $\mathbb P$, and let $g_{\phi,\delta}$ be the distortion of Proposition 5. For every random variable $X$:
--
--   1. for every $\delta>0$ and every increasing $\Lambda:\mathbb R\to(0,1)$,
--   $$\sup_{\mathbb Q\in\mathcal P_\phi(\mathbb P,\delta)}\Lambda\mathrm{VaR}^{\mathbb Q}(X)=\Lambda\mathrm{VaR}^{g_{\phi,\delta}\circ\mathbb P}(X);$$
--   2. for every $\delta>0$ and $\alpha\in(0,1)$, $\sup_{\mathbb Q\in\mathcal P_\phi(\mathbb P,\delta)}\mathrm{VaR}^{\mathbb Q}_\alpha(X)=\mathrm{VaR}^{g_{\phi,\delta}\circ\mathbb P}_\alpha(X)$.
--
--   If moreover $\phi$ is finite on $[0,\infty)$, strictly convex, and $\lim_{x\to\infty}\phi(x)/x=\infty$, then, with $g^{-1}_{\phi,\delta}$ the inverse of $g_{\phi,\delta}$ on $(0,1)$:
--
--   3. for every $\delta>0$ and increasing $\Lambda:\mathbb R\to(0,1)$, $\sup_{\mathbb Q\in\mathcal P_\phi(\mathbb P,\delta)}\Lambda\mathrm{VaR}^{\mathbb Q}(X)=(g^{-1}_{\phi,\delta}\circ\Lambda)\mathrm{VaR}^{\mathbb P}(X)$;
--   4. for every $\delta>0$ and $\alpha\in(0,1)$, $\sup_{\mathbb Q\in\mathcal P_\phi(\mathbb P,\delta)}\mathrm{VaR}^{\mathbb Q}_\alpha(X)=\mathrm{VaR}^{\mathbb P}_{g^{-1}_{\phi,\delta}(\alpha)}(X)$;
--   5. for every increasing $\Lambda:\mathbb R\to(0,1)$,
--   $$\lim_{\delta\downarrow0}\sup_{\mathbb Q\in\mathcal P_\phi(\mathbb P,\delta)}\Lambda\mathrm{VaR}^{\mathbb Q}(X)=\lim_{\delta\downarrow0}(g^{-1}_{\phi,\delta}\circ\Lambda)\mathrm{VaR}^{\mathbb P}(X)=\Lambda\mathrm{VaR}^{+,\mathbb P}(X).$$
--
--   Robustifying $\Lambda$VaR over a $\phi$-divergence ball is thus the same as computing an ordinary $\Lambda$VaR under the reference model with a distorted Lambda function, and as the radius shrinks the robust value tends to the upper version $\Lambda$VaR$^{+}$ rather than to $\Lambda$VaR.
--
--   **Formalization Note** All values, suprema and limits are in $[-\infty,\infty]$ (`EReal`); "$\delta\downarrow0$" is the limit along $\delta\to0^+$, and both limits in item 5 are posed. The second-part hypotheses are: $\phi$ finite on $[0,\infty)$ (the page's "$\phi:[0,\infty)\to\mathbb R$"), strict convexity of $\phi$ on $[0,\infty)$, and $\phi(x)/x\to\infty$. Members of the ball are probability measures. $X$ is any measurable real function, which covers every domain $\mathcal X$ the paper allows. $g^{-1}_{\phi,\delta}(t)$ is formalized as $\sup\{x\in[0,1]: g_{\phi,\delta}(x)\le t\}$, which under the second-part hypotheses is the inverse of $g_{\phi,\delta}$ at every $t\in(0,1)$.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, p. 12, Theorem 2; proof pp. 33–34

import Mathlib
import Definitions.Def_LambdaVaRAmb_Robust_Setting

namespace LambdaVaRAmb.Robust

open MeasureTheory Filter Topology

theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (φ : ℝ → EReal) (hφ : IsPhiFunction φ) :
    (∀ δ : ℝ, 0 < δ → ∀ Λ : ℝ → ℝ, InHI Λ → ∀ X : Ω → ℝ, Measurable X →
        (⨆ Q ∈ phiBall φ P δ, LVaR Λ (probCap Q) X) = LVaR Λ (distortedCap φ δ P) X) ∧
    (∀ δ : ℝ, 0 < δ → ∀ α : ℝ, 0 < α → α < 1 → ∀ X : Ω → ℝ, Measurable X →
        (⨆ Q ∈ phiBall φ P δ, VaRw α (probCap Q) X) = VaRw α (distortedCap φ δ P) X) ∧
    ((∀ x : ℝ, 0 ≤ x → φ x ≠ ⊤) →
      StrictConvexOn ℝ (Set.Ici 0) (fun x => (φ x).toReal) →
      Tendsto (fun x => (φ x).toReal / x) atTop atTop →
      (∀ δ : ℝ, 0 < δ → ∀ Λ : ℝ → ℝ, InHI Λ → ∀ X : Ω → ℝ, Measurable X →
          (⨆ Q ∈ phiBall φ P δ, LVaR Λ (probCap Q) X) = LVaR (gPhiInv φ δ ∘ Λ) (probCap P) X) ∧
      (∀ δ : ℝ, 0 < δ → ∀ α : ℝ, 0 < α → α < 1 → ∀ X : Ω → ℝ, Measurable X →
          (⨆ Q ∈ phiBall φ P δ, VaRw α (probCap Q) X) = VaRw (gPhiInv φ δ α) (probCap P) X) ∧
      (∀ Λ : ℝ → ℝ, InHI Λ → ∀ X : Ω → ℝ, Measurable X →
          Tendsto (fun δ => ⨆ Q ∈ phiBall φ P δ, LVaR Λ (probCap Q) X) (𝓝[>] 0)
            (𝓝 (LVaRPlus Λ (probCap P) X)) ∧
          Tendsto (fun δ => LVaR (gPhiInv φ δ ∘ Λ) (probCap P) X) (𝓝[>] 0)
            (𝓝 (LVaRPlus Λ (probCap P) X)))) := by sorry

end LambdaVaRAmb.Robust
