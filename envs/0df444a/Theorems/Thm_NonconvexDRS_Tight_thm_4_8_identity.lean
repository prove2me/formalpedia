-- Prove2me | Theorems.Thm_NonconvexDRS_Tight_thm_4_8_identity
-- name    : NonconvexDRS.Tight.thm_4_8_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:54.905879+00:00
-- url     : https://prove2.me/theorems/88136d05-8ba5-425e-9d2b-e74868b762ef
-- title:
--   Proof of Theorem 4.8, p. 17 — |u^{k+1} − p| = |1 − λ/(1+γσ)| |uᵏ − p| once uᵏ, u^{k+1} > 1
-- statement:
--   Let $L>0$, $\sigma\in[-L,L]$, $p>1$, $0<\gamma<1/L$ and $\lambda>0$. Let $\varphi_1$ be the function (4.12) with $t=1$, let $\varphi_2=\delta_{\{p\}}$, and let $(s^k,u^k,v^k)_{k\in\mathbb N}$ be a DRS run on $\mathbb R$ with stepsize $\gamma$ and relaxation $\lambda$. If $k$ is such that $u^k>1$ and $u^{k+1}>1$, then
--   $$|u^{k+1}-p|=\Big|1-\frac{\lambda}{1+\gamma\sigma}\Big|\,|u^k-p|,$$
--   and if moreover $\lambda\ge2(1+\gamma\sigma)$, then $|u^{k+1}-p|\ge|u^k-p|$.
--
--   Verbatim (p. 17): "$u^{k+1}+\gamma\frac{L-\sigma}{1+\gamma\sigma}=\frac1{1+\gamma\sigma}s^{k+1}=\frac1{1+\gamma\sigma}(s^k+\lambda(p-u^k))=u^k+\gamma\frac{L-\sigma}{1+\gamma\sigma}+\frac{\lambda}{1+\gamma\sigma}(p-u^k)$, where the identity $s^k=(1+\gamma\sigma)u^k+\gamma(L-\sigma)$ was used, cf. (4.13). Therefore, $|u^{k+1}-p|=\big|1-\frac{\lambda}{1+\gamma\sigma}\big||u^k-p|\ge|u^k-p|$, where the inequality is due to the fact that $\lambda\ge2(1+\gamma\sigma)$."
--
--   This is the expansion step of the paper's counterexample for over-relaxation.
--
--   **Formalization Note** The page uses the identity under "eventually $u^k>1$"; it is needed at both $k$ and $k+1$ (the second branch of (4.13) at $s^{k+1}$), so both are hypotheses. The bound $\gamma<1/L$ is written $\gamma L<1$.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 17, proof of Theorem 4.8, the displayed identity and inequality

import Mathlib
import Definitions.Def_NonconvexDRS_Tight_Setting
open Filter Topology

namespace NonconvexDRS.Tight

theorem thm_4_8_identity (L σ γ lam p : ℝ) (hL : 0 < L) (hσ : -L ≤ σ ∧ σ ≤ L) (hp : 1 < p)
    (hγ : 0 < γ) (hγL : γ * L < 1) (hlam : 0 < lam)
    (s u v : ℕ → ℝ) (hrun : IsDRSRun (phi1Ex L σ 1) (indic ({p} : Set ℝ)) γ lam s u v)
    (k : ℕ) (hk : 1 < u k) (hk1 : 1 < u (k + 1)) :
    |u (k + 1) - p| = |1 - lam / (1 + γ * σ)| * |u k - p| ∧
    (2 * (1 + γ * σ) ≤ lam → |u k - p| ≤ |u (k + 1) - p|) := by sorry

end NonconvexDRS.Tight
