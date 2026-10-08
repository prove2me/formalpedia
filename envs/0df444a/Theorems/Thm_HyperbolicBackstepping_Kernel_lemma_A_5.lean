-- Prove2me | Theorems.Thm_HyperbolicBackstepping_Kernel_lemma_A_5
-- name    : HyperbolicBackstepping.Kernel.lemma_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:26.395082+00:00
-- url     : https://prove2.me/theorems/80f4d089-fd41-4391-9744-fd88a2bff14c
-- title:
--   Lemma A.5, p. 22 — one-step factorial bound for the integral operator
-- statement:
--   Let $\Phi=(\Phi_1,\dots,\Phi_4)$ be the linear integral operator (A.31) of the Goursat system, and let $K_\epsilon$ and $\bar C$ be the constants of (A.35). Fix an integer $n\ge0$ and a number $B\ge0$, and let $\Delta=(\Delta_1,\dots,\Delta_4)$ be continuous on $\mathcal T$. If
--   $$|\Delta_i(x,\xi)|\le B\,\frac{\bar C^n K_\epsilon^n x^n}{n!}\qquad\text{for all } i \text{ and all }(x,\xi)\in\mathcal T,\qquad\text{(A.42)}$$
--   then
--   $$|\Phi_i[\Delta](x,\xi)|\le B\,\frac{\bar C^{n+1}K_\epsilon^{n+1}x^{n+1}}{(n+1)!}\qquad\text{for all } i \text{ and all }(x,\xi)\in\mathcal T.$$
--
--   This is the inductive step of the successive-approximation argument: one application of $\Phi$ raises the factorial order of the bound by one.
--
--   **Formalization Note** The paper states the lemma with its specific constant $\bar\phi$ (the maximum of the source terms, A.35) in place of $B$ and with $n\ge1$; the version here holds for every $B\ge0$ and every $n\in\mathbb N$, which is stronger ($n=0$ is the base case of Proposition A.6). Continuity of $\Delta$ on $\mathcal T$ is added so that the characteristic integrals in $\Phi$ are integrals of continuous functions; the increments $\Delta F^n$ to which the paper applies the lemma are continuous (p. 23).
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, p. 22, Lemma A.5 and (A.42)–(A.44)

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Kernel_Goursat

namespace HyperbolicBackstepping.Kernel

/-- Lemma A.5, p. 22, with the valid base case `n = 0`. -/
theorem lemma_A_5 (D : GoursatData) (n : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (Δ : Fin 4 → ℝ → ℝ → ℝ)
    (hΔcont : ∀ j, ContinuousOn (fun p : ℝ × ℝ => Δ j p.1 p.2) Tri)
    (hΔ : ∀ j : Fin 4, ∀ x ξ : ℝ, (x, ξ) ∈ Tri →
      |Δ j x ξ| ≤ B * (CbarTot D) ^ n * (Keps D) ^ n * x ^ n /
        ((Nat.factorial n : ℕ) : ℝ)) :
    ∀ j : Fin 4, ∀ x ξ : ℝ, (x, ξ) ∈ Tri →
      |PhiOp D Δ j x ξ| ≤
        B * (CbarTot D) ^ (n + 1) * (Keps D) ^ (n + 1) * x ^ (n + 1) /
          ((Nat.factorial (n + 1) : ℕ) : ℝ) := by sorry

end HyperbolicBackstepping.Kernel
