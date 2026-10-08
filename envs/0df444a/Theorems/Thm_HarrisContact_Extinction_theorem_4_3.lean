-- Prove2me | Theorems.Thm_HarrisContact_Extinction_theorem_4_3
-- name    : HarrisContact.Extinction.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:47:58.840163+00:00
-- url     : https://prove2.me/theorems/0dcfe6db-080f-402a-a2b4-06b8dea898cd
-- title:
--   Theorem 4.3, p. 975 — started from a finite set, the contact process has finitely many jumps in every [0, t]
-- statement:
--   Let $d\ge1$, $\mu\ge0$, $\lambda_0=0$ and $\lambda_1,\dots,\lambda_{2d}\ge0$, and let $P_t(\xi,\eta)$ be the minimal transition function of the contact process on finite subsets of $Z_d$ (holding rate $q_\xi$ of (4.4), jump rates (4.5)). Then for every finite $\xi$ and every $t\ge0$,
--   $$\sum_{\eta\in\Xi_0}P_t(\xi,\eta)=1 .$$
--
--   Harris states this as $P_\xi(J_t)=0$, where $J_t$ is the event that $\{\xi_s\}$ has infinitely many jumps in $0\le s\le t$. For the chain on $\Xi_0$, "finitely many jumps on $[0,t]$ almost surely" is exactly the statement that the minimal transition function loses no mass by time $t$. It is what makes the countable-state description of §4 an honest description of the process.
--
--   **Formalization Note** The page's hypotheses are those of a contact process (§2(b), §3): $\lambda_0=0$, $\mu\ge0$, $\lambda_k\ge0$ for $1\le k\le 2d$, and $d\ge1$.
-- source:
--   Harris (Ann. Probab. 2, 1974), Theorem 4.3, p. 975

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.Extinction

/-- Theorem 4.3 (p. 975): started from a finite set, the contact process makes finitely many jumps
on every [0, t] almost surely; in the chain model, the minimal transition function is honest. -/
theorem theorem_4_3 {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) :
    ∀ t : ℝ, 0 ≤ t → ∀ ξ : Config d, ∑' η : Config d, trans μ lam t ξ η = 1 := by sorry

end HarrisContact.Extinction
