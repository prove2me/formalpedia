-- Prove2me | Theorems.Thm_GreenTao_affine_window_varnavides
-- name    : GreenTao.affine_window_varnavides
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T20:38:27.381168+00:00
-- url     : https://prove2.me/theorems/71a47e95-73b1-45d9-a2ff-2d6f88753157
-- title:
--   Varnavides affine-window counting from finite Szemerédi
-- statement:
--   Let $k,L\in\mathbb N$ satisfy $3\le k\le L$, and let $\delta>0$. Assume every $S\subseteq\{0,\ldots,L-1\}$ of cardinality at least $\delta L/2$ contains a $k$-term arithmetic progression with positive common difference. For every prime $m\ge L$ and every $A\subseteq\mathbb Z/m\mathbb Z$ with $|A|\ge\delta m$,
--
--   $$\frac1{m^2}\sum_{x,r\in\mathbb Z/m\mathbb Z}\prod_{j=0}^{k-1}\mathbf 1_A(x+jr)\ge\frac{\delta}{2L^2}.$$
--
--   The count includes zero common differences and counts ordered pairs $(x,r)$. This is the affine-window counting step in the Varnavides argument, separating the combinatorial averaging from the finite-interval Szemerédi input.
-- source:
--   P. Varnavides, On certain sets of positive density, J. London Math. Soc. 34 (1959), 358–360. General k-term affine-window counting argument discussed in Green–Tao, https://arxiv.org/html/math/0404188v6, §2 after Proposition 2.3. This auxiliary conditional formulation makes the finite-interval input and the resulting constant δ/(2L²) explicit; it is not a verbatim numbered theorem of the source.

import Definitions.Def_GreenTao_Pseudorandom
import Mathlib
open scoped BigOperators Topology
open Filter GreenTao

theorem GreenTao.affine_window_varnavides (k L : ℕ) (hk : 3 ≤ k) (hkL : k ≤ L)
    (δ : ℝ) (hδ : 0 < δ)
    (hinterval : ∀ S : Finset ℕ, S ⊆ Finset.range L →
      δ / 2 * (L : ℝ) ≤ (S.card : ℝ) →
      ∃ a d : ℕ, 0 < d ∧ a + (k - 1) * d < L ∧ ∀ j < k, a + j * d ∈ S)
    (m : ℕ+) (hm : Nat.Prime (m : ℕ)) (hLm : L ≤ (m : ℕ))
    (A : Finset (ZMod (m : ℕ))) (hA : δ * (m : ℝ) ≤ (A.card : ℝ)) :
    δ / (2 * (L : ℝ) ^ 2) ≤
      GreenTao.apAvg k (fun x => if x ∈ A then 1 else 0) := by sorry
