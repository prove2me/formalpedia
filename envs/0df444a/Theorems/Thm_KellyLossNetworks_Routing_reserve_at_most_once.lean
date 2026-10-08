-- Prove2me | Theorems.Thm_KellyLossNetworks_Routing_reserve_at_most_once
-- name    : KellyLossNetworks.Routing.reserve_at_most_once
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:10:47.412795+00:00
-- url     : https://prove2.me/theorems/42a6ecf2-b5fd-4713-ad9a-1e78733e4354
-- title:
--   Proof of Thm 4.45, p. 359 — in each triangle, positive capacity is reserved at most once, and only when X₁ > C and X₂, X₃ < C
-- statement:
--   Fix loads $x$ on the edges of the complete graph on $K$ nodes, a capacity $C$ and a scale $D>0$, and let $r_{e,k}$ be the reservation of the pair $e$ through the tandem node $k$:
--   $$
--   r_{e,k}=\frac{(x_e-C)^+(C-x_{ak})^+(C-x_{bk})^+}{(K-2)D}\qquad (e=\{a,b\},\ k\notin e).
--   $$
--   Let $a,b,c$ be three distinct nodes, and consider the three cyclic reservations of the triangle they span: $\{a,b\}$ through $c$, $\{b,c\}$ through $a$, and $\{c,a\}$ through $b$. Then
--
--   1. no two of these three reservations are positive; and
--   2. a reservation $r_{e,k}$ is positive only if $x_e>C$ and both edges of the route of $e$ through $k$ carry loads less than $C$.
--
--   So in each triangle positive capacity is reserved at most once: by the edge with excess flow, through the two edges with excess capacity. This is what makes the reservations of different triangles fit together.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, pp. 358–359, §4.6, proof of Theorem 4.45

import Mathlib
import Definitions.Def_KellyLossNetworks_Routing_Model

open MeasureTheory Filter Topology

namespace KellyLossNetworks.Routing

/-- **Positive capacity is reserved at most once per triangle.** For three distinct nodes
`a, b, c` with edges `e₁ = {a, b}`, `e₂ = {b, c}`, `e₃ = {c, a}`, the three cyclic reservations
`reserve C D x e₁ c`, `reserve C D x e₂ a`, `reserve C D x e₃ b` are such that no two are
positive; and a reservation of `e` via `k` is positive only if `x e > C` and both edges of the
route through `k` carry less than `C`.

Kelly, *Loss networks*, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
§4.6, proof of Theorem 4.45, p. 359 ("Observe that positive capacity will be reserved at most
once, when the labels are such that X₁ > C and X₂, X₃ < C"). -/
theorem reserve_at_most_once {K : ℕ} (C D : ℝ) (hD : 0 < D) (x : Edge K → ℝ)
    (a b c : Fin K) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (e₁ e₂ e₃ : Edge K) (h₁ : e₁.1 = s(a, b)) (h₂ : e₂.1 = s(b, c)) (h₃ : e₃.1 = s(c, a)) :
    ¬ (0 < reserve C D x e₁ c ∧ 0 < reserve C D x e₂ a) ∧
    ¬ (0 < reserve C D x e₂ a ∧ 0 < reserve C D x e₃ b) ∧
    ¬ (0 < reserve C D x e₃ b ∧ 0 < reserve C D x e₁ c) ∧
    ∀ (e : Edge K) (k : Fin K), 0 < reserve C D x e k →
      C < x e ∧ ∀ g, OnDetour e k g → x g < C := by sorry

end KellyLossNetworks.Routing
