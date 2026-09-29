-- Prove2me | Theorems.Thm_HeldWolfeCrowder_Assignment_w_eq_min_assignments
-- name    : HeldWolfeCrowder.Assignment.w_eq_min_assignments
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:52:31.926189+00:00
-- url     : https://prove2.me/theorems/4218e5de-749a-402e-a4eb-cf2364bf22a6
-- title:
--   Eq. (3.4) — the assignment dual w(π) is the minimum of c_A + π·v_A over all n^n assignments
-- statement:
--   Let $A=(a_{ir})$ be a real $n\times n$ cost matrix ($a_{ir}$ = cost of man $i$ on job $r$), and let $w$ be the dual function (3.3),
--   $w(\pi)=\sum_i\pi_i+\sum_r\min_s[a_{sr}-\pi_s]$. For an assignment $A:\{1,\dots,n\}\to\{1,\dots,n\}$ (job $r$ goes to man $A(r)$, not necessarily one-to-one) write $c_A=\sum_r a_{A(r)\,r}$ and $(v_A)_i=1-\#\{r:A(r)=i\}$. Then for every $\pi\in\mathbb R^n$,
--
--   $$w(\pi)=\min\Big\{c_A+\sum_{i=1}^n \pi_i\,(v_A)_i \;:\; A:\{1,\dots,n\}\to\{1,\dots,n\}\Big\},$$
--
--   the minimum being over all $K=n^n$ assignments.
--
--   This exhibits $w$ in the form (2.2) of the paper, $w(\pi)=\min_k\{c_k+\pi\cdot v_k\}$, so that the general subgradient method of Section 2 applies to the assignment dual, with $v_A$ a subgradient at $\pi$ whenever $A$ attains the minimum.
--
--   **Formalization Note** The minimum over the finite, nonempty type `Fin n → Fin n` is `Finset.univ.inf'` (nonemptiness witnessed by the identity), and $\pi\cdot v_A$ is written as the sum $\sum_i \pi_i (v_A)_i$.
-- source:
--   Held, Wolfe & Crowder, Validation of subgradient optimization, Math. Programming 6 (1974), p. 69, Eq. (3.4) ("Then (2.2) holds"), with (2.2) on p. 64

import Mathlib
import Definitions.Def_HeldWolfeCrowder_Assignment_Setting

namespace HeldWolfeCrowder.Assignment

/-- Held–Wolfe–Crowder (1974), p. 69, Eq. (3.4): the dual function (3.3) has the form (2.2),
`w(π) = min_A {c_A + π · v_A}`, the minimum over all `n^n` assignments `A : Fin n → Fin n`,
with `c_A = Σ_r a_{A(r) r}` and `(v_A)_i = 1 − #{r : A(r) = i}`. -/
theorem w_eq_min_assignments {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ) :
    w a π = Finset.univ.inf' ⟨id, Finset.mem_univ _⟩
      (fun A : Fin n → Fin n => assignCost a A + ∑ i, π i * assignVec A i) := by sorry

end HeldWolfeCrowder.Assignment
