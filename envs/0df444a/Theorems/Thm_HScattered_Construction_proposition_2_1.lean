-- Prove2me | Theorems.Thm_HScattered_Construction_proposition_2_1
-- name    : HScattered.Construction.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:11.75598+00:00
-- url     : https://prove2.me/theorems/049c5fc8-2180-404f-8b3b-b0ac96430086
-- title:
--   Proposition 2.1 — h-scattered subspaces are i-scattered for every 0 < i < h
-- statement:
--   Let $V$ be an $r$-dimensional $\mathbb F_{q^n}$-vector space, let $h>1$, and let $U$ be an $h$-scattered $\mathbb F_q$-subspace of $V$. Then
--
--   $$
--   U \text{ is } i\text{-scattered for every integer } 0<i<h ,
--   $$
--
--   and in particular $U$ is $1$-scattered.
--
--   So the $h$-scattered subspaces form a decreasing chain of classes inside the spanning scattered subspaces. The result is used repeatedly to pass from $h$-scattered to $s$-scattered for smaller $s$, for instance in the proof of the direct-sum theorem (Theorem 2.4).
--
--   **Formalization Note** "$i$-scattered" includes the range $0<i<r$ of Definition 1.1; the hypothesis $0<i$ is the lower end of that range, and $i<h<r$ gives the upper end.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 3, Proposition 2.1

import Mathlib
import Definitions.Def_HScattered_Construction_IsHScattered

namespace HScattered.Construction

/-- Proposition 2.1 (arXiv:1906.10590v2, p. 3): for `h > 1`, an h-scattered `𝔽_q`-subspace is
i-scattered for every `0 < i < h`; in particular it is 1-scattered. -/
theorem proposition_2_1 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (hh : 1 < h) (U : Submodule F V) (hU : HScattered.Bound.IsHScattered F K h U) :
    (∀ i : ℕ, 0 < i → i < h → HScattered.Bound.IsHScattered F K i U) ∧ HScattered.Bound.IsHScattered F K 1 U := by sorry

end HScattered.Construction
