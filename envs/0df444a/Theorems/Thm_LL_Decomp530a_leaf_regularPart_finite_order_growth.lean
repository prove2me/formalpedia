-- Prove2me | Theorems.Thm_LL_Decomp530a_leaf_regularPart_finite_order_growth
-- name    : LL_Decomp530a.leaf_regularPart_finite_order_growth
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-17T15:38:08.212999+00:00
-- url     : https://prove2.me/theorems/5a6ae6c1-6e89-4d08-86d9-524776dcc22c
-- title:
--   Finite order growth of the pole-subtracted L-function
-- statement:
--   Let $0<\delta<1/2$, let $q\ge1$ and let $\chi$ be a Dirichlet character modulo $q$. Then there exist real constants $C>0$ and $c>0$ such that for every complex $s$ with $-\delta\le\operatorname{Re}s\le1+\delta$ one has $|R_\chi(s)|\le C\exp\big(|\operatorname{Im}s|^{c}\big)$, where $R_\chi$ is $L(s,\chi)$ with the pole of the principal character subtracted.
-- source:
--   Rademacher 1959, Math. Z. 72, p. 195, display 3.1, applied in Section 6, pp. 198 and 199; input to Baker, Harman and Pintz 1997, Lemma 8.

import Mathlib
import Definitions.Def_LL_Decomp530a_regularPart

open Classical Complex Set Filter ZMod
open scoped Topology

namespace LL_Decomp530a
theorem leaf_regularPart_finite_order_growth {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ s : ℂ,
      -δ ≤ s.re → s.re ≤ 1 + δ →
      ‖regularPart χ s‖ ≤ C * Real.exp (|s.im| ^ c) := by sorry
end LL_Decomp530a
