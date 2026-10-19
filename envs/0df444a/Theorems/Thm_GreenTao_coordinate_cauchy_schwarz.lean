-- Prove2me | Theorems.Thm_GreenTao_coordinate_cauchy_schwarz
-- name    : GreenTao.coordinate_cauchy_schwarz
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T21:16:17.461015+00:00
-- url     : https://prove2.me/theorems/2fe78fc7-3dc5-4a61-a818-686f32e1547a
-- title:
--   Weighted Cauchy–Schwarz with coordinate duplication
-- statement:
--   Let $A,B$ be finite sets, let $G,w:A\to\mathbb R$ and $H:A\times B\to\mathbb R$, and suppose $w\ge0$ and $|G|\le w$. With uniform averages,
--
--   $$\left|\mathbb E_a G(a)\,\mathbb E_b H(a,b)\right|^2\le(\mathbb E_a w(a))\,\mathbb E_{a,b,c}w(a)H(a,b)H(a,c).$$
--
--   This is the weighted coordinate-duplication step of the repeated Cauchy–Schwarz argument: $a$ collects the other variables and $b,c$ are independent copies of the coordinate being eliminated. It is valid for signed $G,H$ and nonnegative weights that can vanish.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §5 Lemma 5.4, equation (5.19), and its proof by separating a coordinate and applying weighted Cauchy–Schwarz. This is its coordinate-invariant finite averaging step, not the full indexed J_d/P_d specialization.

import Definitions.Def_GreenTao_Pseudorandom
import Mathlib
open scoped BigOperators Topology
open Filter GreenTao

theorem GreenTao.coordinate_cauchy_schwarz {α β : Type} [Fintype α] [Fintype β]
    (G w : α → ℝ) (H : α → β → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hG : ∀ a, |G a| ≤ w a) :
    (avg fun a => G a * avg (H a)) ^ 2 ≤
      avg w * avg (fun a => avg fun b => avg fun c => w a * H a b * H a c) := by sorry
