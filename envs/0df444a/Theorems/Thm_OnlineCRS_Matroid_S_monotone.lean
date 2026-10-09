-- Prove2me | Theorems.Thm_OnlineCRS_Matroid_S_monotone
-- name    : OnlineCRS.Matroid.S_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:24:11.722575+00:00
-- url     : https://prove2.me/theorems/75211434-8aac-45f0-94ec-5dbba566019e
-- title:
--   §2.1.1, p. 11 — the set S grows as activation probabilities grow
-- statement:
--   Let $M$ be a matroid on the finite ground set $N$ and let $b\in[0,1]$. For $x\in[0,1]^N$ let $R(x)$ be the random set containing each $e$ independently with probability $x_e$, and let $S(x)=S_{|N|}$, where $S_0=\varnothing$ and
--   $$S_i=\{e\in N : \Pr[e\in\operatorname{span}((R(x)\cup S_{i-1})\setminus\{e\})]>b\}\qquad(i\ge1).$$
--   If $x,y\in[0,1]^N$ satisfy $x_e\le y_e$ for every $e\in N$, then
--
--   $$S(x)\subseteq S(y).$$
--
--   In words, the set $S$ can only grow when coordinates of $x$ are increased. Together with the fact that every point of the matroid polytope lies below a point of the base polytope, this lets the termination analysis of the chain construction assume $x\in b\cdot P_{\mathcal B}$.
--
--   **Formalization Note** The statement holds for any finite matroid, so no ground-set or loop hypothesis is imposed; the bounds $0\le x\le y\le 1$ make both $R(x)$ and $R(y)$ genuine random sets.
-- source:
--   arXiv:1508.00142v2, §2.1.1, p. 11, first paragraph

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Construction

namespace OnlineCRS.Matroid

/-- arXiv:1508.00142v2, §2.1.1, p. 11, first paragraph. -/
theorem S_monotone {α : Type} [Fintype α] [DecidableEq α]
    (M : Matroid α) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (x y : α → ℝ) (hx0 : ∀ e, 0 ≤ x e) (hxy : ∀ e, x e ≤ y e)
    (hy1 : ∀ e, y e ≤ 1) :
    Sfin M x b ⊆ Sfin M y b := by sorry

end OnlineCRS.Matroid
