-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_proposition_3_4_perturbed
-- name    : HubSpokePricing.Lagrangian.proposition_3_4_perturbed
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-30T19:12:42.341013+00:00
-- url     : https://prove2.me/theorems/6f71bb8d-1cc9-4f50-97b5-0fcad1974381
-- title:
--   Proposition 3.4 for the perturbed dual (11) — Σᵢ 𝔼[X̃ᵢ(δ)] ≤ m − δ with complementary slackness
-- statement:
--   Let $N$ be a hub-and-spoke network satisfying the standing assumptions (Assumption 2.1), with $n$ spokes and $m$ resources. For a dual price $\lambda\ge0$, the spoke problem (6) of spoke $i$ has optimal value $h_i^\lambda$, and $\bar V^\lambda=m\lambda+\sum_i h_i^\lambda$. For $0\le\delta<m$, the perturbed Lagrangian dual is
--   $$V^{\mathrm R}(\delta)=\min_{\lambda\ge0}\ \bar V^\lambda-\delta\lambda .\tag{11}$$
--
--   Let $\lambda^*=\lambda^*(\delta)$ be an optimal solution of (11). For each spoke $i$, let $p_i$ be the stationary distribution of an optimal solution of (6) at $\lambda^*$, so that $\mathbb E[\tilde X_i(\delta)]=\sum_{x=0}^m x\,p_i(x)$. Then the optimality (complementary slackness) conditions hold with $m$ replaced by $m-\delta$:
--   $$\sum_{i=1}^n\sum_{x=0}^m x\,p_i(x)\le m-\delta,\qquad \lambda^*\Big(m-\delta-\sum_{i=1}^n\sum_{x=0}^m x\,p_i(x)\Big)=0 .$$
--   In words, the expected number of resources the relaxed system keeps at the spokes leaves at least $\delta$ resources at the hub in expectation. The constraint is tight whenever $\lambda^*>0$.
--
--   This is the "only if" direction of Proposition 3.4 (condition (10)), applied to the perturbed dual (11) as the paper does in §3.4 and §4.2. It is what gives $0\le\mu\le m-\delta$ in the proof of Proposition 4.6. The paper derives it in Appendix A.6 from Danskin's theorem: the optimal distribution of (6) is unique (Proposition B.8), so $\bar V^\lambda-\delta\lambda$ is differentiable with derivative $(m-\delta)-\sum_i\mathbb E[\tilde X_i^\lambda]$.
--
--   **Formalization Note.** `spokeMean (sol i)` is $\sum_x x\,p_i(x)$, and `IsDualOpt N δ lam` says that `lam` minimizes $\bar V^\lambda-\delta\lambda$ over $\lambda\ge0$. The statement covers every choice of optimal spoke solutions at $\lambda^*$, which relies on the uniqueness in Proposition B.8.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, Proposition 3.4 and condition (10), pp. 15–16, applied to (11) with m replaced by m − δ (§3.4 p. 16, §4.2 p. 18, Appendix A.10 p. 53: '0 < µ ≤ m − δ'); proof in Appendix A.6 (pp. 46–47) via Proposition B.8 (uniqueness of the optimal distribution of (6)) and Appendix A.11.1

import Mathlib
import Definitions.Def_HubSpokePricing_Lagrangian_Model

namespace HubSpokePricing.Lagrangian

/-- Proposition 3.4 (p. 16) for the perturbed dual (11) (`m` replaced by `m − δ`, §3.4 and §4.2,
pp. 16–18; Appendix A.6, p. 47; A.11, p. 59): if `λ*(δ)` is optimal for (11) and `p_i` are optimal
solutions of (6) at `λ*(δ)`, then `∑ᵢ 𝔼[X̃ᵢ(δ)] ≤ m − δ`, with equality whenever `λ*(δ) > 0`. -/
theorem proposition_3_4_perturbed (N : Network) (hN : N.Standing) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδm : δ < N.m) (lam : ℝ) (hlam : IsDualOpt N δ lam)
    (sol : Fin N.n → SpokeSol N.m) (hsol : ∀ i, SpokeOptimal N lam i (sol i)) :
    ∑ i, spokeMean (sol i) ≤ (N.m : ℝ) - δ ∧
      lam * ((N.m : ℝ) - δ - ∑ i, spokeMean (sol i)) = 0 := by sorry

end HubSpokePricing.Lagrangian
