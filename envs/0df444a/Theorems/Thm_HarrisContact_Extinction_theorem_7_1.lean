-- Prove2me | Theorems.Thm_HarrisContact_Extinction_theorem_7_1
-- name    : HarrisContact.Extinction.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:13:27.018696+00:00
-- url     : https://prove2.me/theorems/039a6b70-c24f-4783-92cf-aead90c1aef4
-- title:
--   Theorem 7.1, p. 981 — a contact process with (2d − 1)λ_k < kμ, k = 1, …, 2d, dies out: p_∞(ξ) = 0 for finite ξ
-- statement:
--   Let $\{\xi_t\}$ be a contact process on $Z_d$, $d\ge1$: each infected site recovers at rate $\mu\ge0$, and each healthy site with $k$ infected neighbours becomes infected at rate $\lambda_k\ge0$, with $\lambda_0=0$. Suppose
--   $$(2d-1)\lambda_k<k\mu,\qquad k=1,2,\dots,2d .$$
--   Then for every finite initial set $\xi\subset Z_d$,
--   $$p_\infty(\xi)=\lim_{t\to\infty}P_\xi\{\xi_t\neq\varnothing\}=0,$$
--   that is, the process dies out almost surely.
--
--   This is Harris's sufficient condition for extinction of the contact process; for the linear case $\lambda_k=k\lambda$, $\mu=1$ it reads $(2d-1)\lambda<1$. In the linear case it bounds the critical infection rate of the contact process from below by $1/(2d-1)$.
--
--   **Formalization Note** The process is the countable-state chain on finite subsets with rates (4.4)–(4.5), and $p_\infty(\xi)=\inf_{t\ge0}\bigl(1-P_t(\xi,\varnothing)\bigr)$ in $[0,\infty]$, where $P_t$ is the minimal transition function; so the conclusion is absorption at $\varnothing$, not loss of mass. The condition is imposed for $k=1,\dots,2d$, the only indices that occur, and $2d-1$ is the real number $2d-1$. With $k=1$ the condition forces $\mu>0$.
-- source:
--   Harris (Ann. Probab. 2, 1974), Theorem 7.1, p. 981

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.Extinction

/-- Theorem 7.1 (p. 981): if (2d − 1)λ_k < kμ for k = 1, …, 2d, then p_∞(ξ) = 0 for every
finite ξ. -/
theorem theorem_7_1 {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (hsub : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * d → (2 * (d : ℝ) - 1) * lam k < k * μ) :
    ∀ ξ : Config d, survInf μ lam ξ = 0 := by sorry

end HarrisContact.Extinction
