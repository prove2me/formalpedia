-- Prove2me | Theorems.Thm_KendallBD_Sol_geometric_solution
-- name    : KendallBD.Sol.geometric_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:25:52.214903+00:00
-- url     : https://prove2.me/theorems/de700cc9-c426-47e1-9a38-82c73d1bf67c
-- title:
--   §2, (8), (10a)–(12), pp. 3–4 — geometric transient law solves the model
-- statement:
--   Let $\lambda(t),\mu(t)\ge0$ be continuous per-individual birth and death rates. Define $P_n(t)$ using $\rho$, $W$, $\xi_t$, and $\eta_t$ as in equations (8) and (10a)–(12). Then $P_1(0)=1$ and $P_n(0)=0$ for $n\ne1$. For every $t\ge0$, the sequence is a probability law, and it satisfies the forward equations
--   $$
--   P_0'(t)=\mu(t)P_1(t),\qquad
--   P_n'(t)=(n+1)\mu(t)P_{n+1}(t)+(n-1)\lambda(t)P_{n-1}(t)-n(\lambda(t)+\mu(t))P_n(t)\quad(n\ge1).
--   $$
--   This is Kendall’s geometric distribution with a modified zero term as a solution of his one-ancestor transient population model.
--
--   **Formalization Note** The proof obligation includes nonnegative masses and `HasSum` to one at each nonnegative time, as well as the differential equations. Rate continuity on $\mathbb R$ is used only to express derivatives at nonnegative time.
-- source:
--   Kendall, On the generalized "birth-and-death" process, Ann. Math. Statist. 19 (1948), §2, (2)–(4), (8), (10a)–(12), pp. 2–4

import Mathlib
import Definitions.Def_KendallBD_Sol_Setting

open Filter
open scoped Topology

namespace KendallBD.Sol

theorem geometric_solution (lam mu : ℝ → ℝ) (hlam : Continuous lam) (hmu : Continuous mu)
    (hlam0 : ∀ t, 0 ≤ t → 0 ≤ lam t) (hmu0 : ∀ t, 0 ≤ t → 0 ≤ mu t) :
    InitialCondition (P lam mu) ∧ SolvesForward lam mu (P lam mu) ∧
      ∀ t, 0 ≤ t → (∀ n, 0 ≤ P lam mu n t) ∧
        HasSum (fun n : ℕ => P lam mu n t) 1 := by sorry

end KendallBD.Sol
