-- Prove2me | Theorems.Thm_Localization_Away_existsUnique_forall_algebraMap_eq_of_span_eq_top
-- name    : Localization.Away.existsUnique_forall_algebraMap_eq_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/9b43ed2b-471a-5054-bf7b-312ad8320e7a
-- title:
--   Gluing ring elements along a standard open cover
-- statement:
--   Let $B$ be a commutative ring, let $n$ be a natural number and let $g : \mathrm{Fin}\,n \to B$ be a finite family of elements of $B$ whose range generates the unit ideal, $\mathrm{Ideal.span}(\mathrm{range}\,g) = \top$. Suppose given, for each index $i$, an element $x_i$ of the localisation `Localization.Away (g i)` of $B$ away from $g_i$, i.e. of $B[1/g_i]$. Assume these elements are pairwise compatible on overlaps: for all indices $i$ and $j$, the image of $x_i$ under the canonical map `IsLocalization.Away.awayToAwayRight` from $B[1/g_i]$ to `Localization.Away (g i * g j)` $= B[1/(g_ig_j)]$ (the map inverting the extra factor $g_j$) coincides with the image of $x_j$ under the canonical map `IsLocalization.Away.awayToAwayLeft` from $B[1/g_j]$ to the same ring $B[1/(g_ig_j)]$ (the map inverting the extra factor $g_i$). Then there is exactly one element $b$ of $B$ such that for every $i$ the image of $b$ under $\mathrm{algebraMap}\,B\,(B[1/g_i])$ equals $x_i$.
--
--   This is the sheaf axiom for the structure sheaf of $\operatorname{Spec} B$ restricted to a finite cover by basic open sets, in purely ring-theoretic form: exactness of $0 \to B \to \prod_i B[1/g_i] \rightrightarrows \prod_{i,j} B[1/(g_ig_j)]$ for $g_1,\dots,g_n$ generating the unit ideal. It is used in the Čerednik–Drinfel'd part of the development to assemble points of moduli functors and morphisms of rigidified objects from data given on a standard affine cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Localization_Away_existsUnique_forall_algebraMap_eq_of_span_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Localization.Away.existsUnique_forall_algebraMap_eq_of_span_eq_top
    {B : Type} [CommRing B] {n : ℕ} (g : Fin n → B) (hg : Ideal.span (Set.range g) = ⊤)
    (x : ∀ i : Fin n, Localization.Away (g i))
    (hx : ∀ i j : Fin n, IsLocalization.Away.awayToAwayRight (S := Localization.Away (g i)) (g i) (g j)
        (P := Localization.Away (g i * g j)) (x i) =
      IsLocalization.Away.awayToAwayLeft (S := Localization.Away (g j)) (g j) (g i)
        (P := Localization.Away (g i * g j)) (x j)) :
    ∃! b : B, ∀ i : Fin n, algebraMap B (Localization.Away (g i)) b = x i := by sorry
