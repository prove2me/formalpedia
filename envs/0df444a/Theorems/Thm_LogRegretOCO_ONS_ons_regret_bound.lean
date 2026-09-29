-- Prove2me | Theorems.Thm_LogRegretOCO_ONS_ons_regret_bound
-- name    : LogRegretOCO.ONS.ons_regret_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:37:47.352253+00:00
-- url     : https://prove2.me/theorems/8de70aed-5c8c-478c-8995-db59d7211b37
-- title:
--   Theorem 2 — Online Newton Step has regret at most 5(1/α + GD) n log T when n log T ≥ 4
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^n$ be a nonempty, closed, bounded and convex decision set with $\|x-y\|\le D$ for all $x,y\in\mathcal P$. Let the cost functions $f_1,f_2,\dots:\mathbb R^n\to\mathbb R$ be differentiable at every point of $\mathcal P$, with gradients bounded by $\|\nabla f_t(x)\|\le G$ on $\mathcal P$, and $\alpha$-exp-concave on $\mathcal P$: $x\mapsto\exp(-\alpha f_t(x))$ is concave on $\mathcal P$ for every $t$. Assume $G,D,\alpha>0$.
--
--   Let $x_1,x_2,\dots$ be any run of the **Online Newton Step** with $\beta=\tfrac12\min\{1/(4GD),\alpha\}$ and $\varepsilon=1/(\beta^2D^2)$: $x_1\in\mathcal P$ is arbitrary and $x_{t+1}=\Pi^{A_t}_{\mathcal P}\big(x_t-\frac1\beta A_t^{-1}\nabla_t\big)$ with $\nabla_t=\nabla f_t(x_t)$ and $A_t=\sum_{i=1}^t\nabla_i\nabla_i^\top+\varepsilon I_n$. Then for every horizon $T$ with $n\log T\ge4$ and every comparator $u\in\mathcal P$,
--   $$
--   \sum_{t=1}^{T}\big(f_t(x_t)-f_t(u)\big)\ \le\ 5\Big(\frac1\alpha+GD\Big)\,n\log T .
--   $$
--
--   This is the logarithmic regret guarantee for exp-concave losses, which include the log-loss of universal portfolio management; it needs only gradient information and one generalized projection per round.
--
--   **Formalization Note** The paper prints the bound for every $T$ without the condition $n\log T\ge4$, and as printed it is false at $T=1$: with $n=1$, $\mathcal P=[-1,1]$, $f_1(x)=x^2$, $\alpha=\tfrac12$, $G=D=2$ and $x_1=1$ the regret is $1$ while the right side is $0$. The paper's proof establishes $\mathrm{Regret}_T\le\frac1{2\beta}\big(n\log(TG^2\beta^2D^2+1)+1\big)\le 4(\frac1\alpha+GD)(n\log T+1)$ for $T\ge2$; the final step "this gives the stated regret bound" drops the additive $\frac1{2\beta}$. The printed constant $5$ follows exactly when $n\log T\ge4$, which is the added hypothesis (it forces $n\ge1$ and $T\ge2$). Regret is stated against every $u\in\mathcal P$, equivalent to the paper's minimum over $\mathcal P$ (attained, since $\mathcal P$ is compact) and avoiding a real infimum. $G,D,\alpha>0$ is the non-degeneracy that the printed formulas for $\beta$ and $\varepsilon$ presuppose. The printed "$f_t:\mathcal P\to\mathbb R^n$" is a typo for $\mathbb R$. The cost functions are ambient functions on $\mathbb R^n$, differentiable at the points of $\mathcal P$; the paper's standing assumptions of convexity and twice differentiability are not needed and are omitted. $D$ is used only as an upper bound on distances in $\mathcal P$.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 176, Theorem 2 (proof pp. 177–179); DOI 10.1007/s10994-007-5016-8

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_Basic
import Definitions.Def_LogRegretOCO_ONS_Run

namespace LogRegretOCO.ONS

/-- Theorem 2 (Hazan–Agarwal–Kale 2007, p. 176), with the added hypothesis `n log T ≥ 4`.
Let `P ⊆ ℝⁿ` be nonempty, closed, bounded and convex with `‖x − y‖ ≤ D` on `P`; let every cost
`f_t` be differentiable on `P` with `‖∇f_t‖ ≤ G` there and `α`-exp-concave on `P`. Then every run
of the Online Newton Step with `β = ½ min{1/(4GD), α}` and `ε = 1/(β²D²)` satisfies, for every
horizon `T` with `n log T ≥ 4` and every comparator `u ∈ P`,
`Σ_{t=1}^T (f_t(x_t) − f_t(u)) ≤ 5 (1/α + GD) n log T`. -/
theorem ons_regret_bound {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (hP_ne : P.Nonempty) (hP_closed : IsClosed P) (hP_bdd : Bornology.IsBounded P)
    (hP_conv : Convex ℝ P)
    (G D α : ℝ) (hG : 0 < G) (hD : 0 < D) (hα : 0 < α)
    (hdiam : ∀ x ∈ P, ∀ y ∈ P, ‖x - y‖ ≤ D)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hdiff : ∀ t, ∀ x ∈ P, DifferentiableAt ℝ (f t) x)
    (hgrad : ∀ t, ∀ x ∈ P, ‖gradient (f t) x‖ ≤ G)
    (hexp : ∀ t, ConcaveOn ℝ P (fun x => Real.exp (-α * f t x)))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsONSRun P G D α f x)
    (T : ℕ) (hT : 4 ≤ (n : ℝ) * Real.log T) :
    ∀ u ∈ P, ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t u) ≤
      5 * (1 / α + G * D) * n * Real.log T := by sorry

end LogRegretOCO.ONS
