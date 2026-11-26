-- Prove2me | Theorems.Thm_LefebvreVariations_kakeya_set_conjecture_dim_one
-- name    : LefebvreVariations.kakeya_set_conjecture_dim_one
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:43:45.442803+00:00
-- url     : https://prove2.me/theorems/959f50ad-cf02-4f92-834e-d95541f8d1e6
-- title:
--   Lefebvre's variations, No. 59 — on a theme by Kakeya: Kakeya sets in dimension one have Hausdorff dimension one
-- statement:
--   A set $S\subseteq\mathbb{R}^n$ is a *Kakeya set* if for every unit vector $v$ there is a point $a$ with $[a,a+v]\subseteq S$, where $[a,a+v]=\{a+tv: 0\le t\le 1\}$ is the unit segment in direction $v$. For $n=1$:
--   $$
--   \forall S\subseteq\mathbb{R}\;\Big(\big(\forall v\in\mathbb{R},\ |v|=1\ \Rightarrow\ \exists a\in\mathbb{R},\ [a,a+v]\subseteq S\big)\ \Longrightarrow\ \dim_H S = 1\Big).
--   $$
--
--   This is the instance $n=1$ of the Kakeya set conjecture, which asserts that every Kakeya set in $\mathbb{R}^n$ has Hausdorff dimension $n$. The conjecture is classical for $n=2$ and open for $n\ge 3$ (in dimension $3$ a proof has been announced by Wang and Zahl). In dimension one the statement is elementary: a Kakeya set contains a unit interval, and that is all that is used.
--
--   **Formalization Note** The statement is `KakeyaSetConjectureDim 1` from `Definitions.Def_FCP_Kakeya`: for every `S : Set (EuclideanSpace ℝ (Fin 1))` satisfying `IsKakeya S`, `dimH S = 1` (the right-hand side is the natural number `1` cast to `ℝ≥0∞`). `IsKakeya S` means: for every `v : EuclideanSpace ℝ (Fin 1)` with `‖v‖ = 1` there is `a` with `affineSegment ℝ a (a + v) ⊆ S`. No compactness or boundedness of `S` is assumed, and no measurability. Both directions of the equality are asserted (`dimH S ≤ 1` and `1 ≤ dimH S`).
--
--   **Why this is a variation.** Variation on the open FCP.Kakeya.kakeya_set_conjecture (Kakeya sets in $\mathbb R^n$ have Hausdorff dimension $n$). It is the instance $n=1$, where a Kakeya set contains a unit segment; it is the degenerate first case of the parent, stated in the parent's own definitions, and it fixes the pattern that the higher-dimensional cases must reproduce.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent: FCP.Kakeya.kakeya_set_conjecture (Kakeya set conjecture in R^n, status Open on the platform); this statement is its instance n = 1, with the parent's own definitions IsKakeya and KakeyaSetConjectureDim from Definitions.Def_FCP_Kakeya. Note that the parent's hypothesis 0 < n includes n = 1, so this is literally a special case of the parent.
--   The proof is elementary (a Kakeya set contains a unit segment, hence a set with nonempty interior in R, and dim_H R = 1); it is an elementary consequence of the definitions and needs no source.
--   Context, cited from memory and not re-checked: the case n = 2 is due to R. O. Davies, 'Some remarks on the Kakeya problem', Proc. Cambridge Philos. Soc. 69 (1971), 417-421 (it is on the platform as FCP.Kakeya.kakeya_two_dim). The announced proof for n = 3 is due to H. Wang and J. Zahl (2025); the platform has WangZahlKakeya.kakeya_set_conjecture_R3 (Open). Neither of these is part of the formal statement, and the exact title, pages and year given here are from memory.

import Mathlib
import Definitions.Def_FCP_Kakeya

set_option autoImplicit false

namespace LefebvreVariations

open FCP.Kakeya

/-- **The Kakeya set conjecture in dimension one.** Every Kakeya set in `ℝ¹` has Hausdorff
dimension `1`: the instance `n = 1` of the parent `FCP.Kakeya.kakeya_set_conjecture`. (Elementary: a
Kakeya set contains a unit interval; the conjecture is classical in dimension 2 (Davies, *Proc.
Cambridge Philos. Soc.* 69 (1971) 417–421, cited from memory) and open for `n ≥ 3`.) -/
theorem kakeya_set_conjecture_dim_one : KakeyaSetConjectureDim 1 := by sorry

end LefebvreVariations
