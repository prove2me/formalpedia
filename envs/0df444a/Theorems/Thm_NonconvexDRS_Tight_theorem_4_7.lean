-- Prove2me | Theorems.Thm_NonconvexDRS_Tight_theorem_4_7
-- name    : NonconvexDRS.Tight.theorem_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:50.604327+00:00
-- url     : https://prove2.me/theorems/ae746252-f829-40a1-ad51-6954d66c927f
-- title:
--   Theorem 4.7 (corrected to γ > 1/L), p. 16 — for every L > 0 and σ ∈ [−L, L] there are φ₁, φ₂ on which no DRS run with γ > 1/L has vanishing residual
-- statement:
--   **Theorem 4.7 (Necessity of $\gamma<1/L_{\varphi_1}$).** Let $p\ge1$, $L>0$ and $\sigma\in[-L,L]$. There exist $\varphi_1:\mathbb R^p\to\mathbb R$ and $\varphi_2:\mathbb R^p\to\overline{\mathbb R}$ such that
--
--   1. $\varphi_1$ is $L$-smooth and $\sigma$-hypoconvex;
--   2. $\varphi_2$ is proper and lower semicontinuous;
--   3. $\operatorname{arg\,min}(\varphi_1+\varphi_2)\neq\emptyset$;
--   4. for every $\gamma>1/L$, every $\lambda>0$ and every DRS run $(s^k,u^k,v^k)_{k\in\mathbb N}$ with stepsize $\gamma$ and relaxation $\lambda$ (from any starting point $s^0$ and with any selection from the proximal sets),
--   $$\|s^k-s^{k+1}\|\not\to0\qquad\text{as }k\to\infty.$$
--
--   Together with the paper's convergence theorem for $\gamma<1/L$, this shows that the stepsize bound $\gamma<1/L_{\varphi_1}$ cannot be enlarged under Assumption I without further structure on $\varphi_2$.
--
--   **Formalization Note** The page states p4 for $\gamma\ge1/L$. That is false at $\gamma=1/L$ for every pair satisfying p1–p3: if $x^\star$ minimizes $\varphi_1+\varphi_2$ and $s^\star=x^\star+\gamma\nabla\varphi_1(x^\star)$, then the constant run $s^k=s^\star$, $u^k=v^k=x^\star$ is a DRS run with zero residual. In the paper's own example ($L=1$, $\sigma=0$, $t=2$, $\gamma=1$) this is $s^k=2$, $u^k=v^k=1$. The theorem is therefore stated for $\gamma>1/L$, written $1<\gamma L$. The dimension $p\ge1$ is added: for $p=0$ every run is constant. The paper's construction is one-dimensional; for $p\ge1$ it extends by adding $\tfrac L2\|(x_2,\dots,x_p)\|^2$ to $\varphi_1$ and taking $\varphi_2=\delta_{\{\pm e_1\}}$. When $\gamma\ge1/[\sigma]_-$ the proximal sets of $\varphi_1$ may be empty, and then no run exists; the claim then holds because there is nothing to check, as on the page. A run is any selection, so the claim covers every choice at points where a proximal set has two elements.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 16, Theorem 4.7 (p4 corrected from γ ≥ 1/L to γ > 1/L)

import Mathlib
import Definitions.Def_NonconvexDRS_Tight_Setting
open Filter Topology

namespace NonconvexDRS.Tight

theorem theorem_4_7 (p : ℕ) (hp : 1 ≤ p) (L σ : ℝ) (hL : 0 < L) (hσ : -L ≤ σ ∧ σ ≤ L) :
    ∃ (φ₁ : EuclideanSpace ℝ (Fin p) → ℝ) (φ₂ : EuclideanSpace ℝ (Fin p) → EReal),
      (IsLSmooth φ₁ L ∧ IsHypoconvex φ₁ σ) ∧
      (IsProper φ₂ ∧ LowerSemicontinuous φ₂) ∧
      (∃ xs, ∀ x, (φ₁ xs : EReal) + φ₂ xs ≤ (φ₁ x : EReal) + φ₂ x) ∧
      ∀ (γ lam : ℝ), 1 < γ * L → 0 < lam →
        ∀ s u v : ℕ → EuclideanSpace ℝ (Fin p), IsDRSRun φ₁ φ₂ γ lam s u v →
          ¬ Tendsto (fun k => ‖s k - s (k + 1)‖) atTop (𝓝 0) := by sorry

end NonconvexDRS.Tight
