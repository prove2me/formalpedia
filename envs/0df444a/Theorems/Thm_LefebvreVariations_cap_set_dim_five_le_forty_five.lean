-- Prove2me | Theorems.Thm_LefebvreVariations_cap_set_dim_five_le_forty_five
-- name    : LefebvreVariations.cap_set_dim_five_le_forty_five
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:02:04.547163+00:00
-- url     : https://prove2.me/theorems/55ca6133-6146-5d56-92dc-d556e5d2d7c3
-- title:
--   Lefebvre's variations, No. 130 — on a theme by Jordan Ellenberg and Dion Gijswijt: cap sets in F_3^5 have at most forty-five points
-- statement:
--   Let $A\subseteq\mathbb{F}_3^{5}$ contain no three distinct points $x,y,z$ with $x+y+z=0$ (a cap set, equivalently a set with no three-term arithmetic progression). Then
--   $$
--   |A|\le 45.
--   $$
--   This is sharp: the maximum size of a cap set in $\mathbb{F}_3^{5}$ is exactly $45$.
--
--   **Formalization Note** The hypothesis is the one of the platform's `cap_set_bound`: for all $x,y,z\in A$, $x+y+z=0$ implies $x=y$ (in characteristic $3$ this forces $x=y=z$). The ambient space is `Fin 5 → ZMod 3` and the conclusion is the natural-number inequality `A.card ≤ 45`.
--
--   **Why this is a variation.** A variation on the platform's open `cap_set_bound` (|A| <= 2.756^n for cap sets in F_3^n). It fixes the dimension n = 5 and states the exact maximum size, which is a sharper finite fact than the asymptotic bound. The parent, whose true growth rate is unknown, remains open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   The maximum size of a cap set in AG(5,3) is 45: Y. Edel, S. Ferret, I. Landjev and L. Storme, The classification of the largest caps in AG(5,3), J. Combin. Theory Ser. A (2002) (title, authors, journal and year verified by web search; volume and pages not). The sequence of maximal cap sizes 2, 4, 9, 20, 45, 112 for dimensions 1 to 6 is tabulated in Follett, Kalail, McMahon, Pelland, Won, Partitions of AG(4,3) into maximal caps, arXiv:1302.4703 (verified by web search). Parent: the cap set bound of Ellenberg and Gijswijt, Annals of Math. 185 (2017), on the platform as `cap_set_bound`; pages not verified.

import Mathlib

namespace LefebvreVariations

/-- A cap set in `F_3^5` has at most `45` points (exact maximum 45). Source: Y. Edel, S. Ferret, I. Landjev, L. Storme, The classification of the largest caps in AG(5,3), J. Combin. Theory Ser. A 99 (2002) 95-110 (the maximum is 45) (cited from memory). -/
theorem cap_set_dim_five_le_forty_five
    (A : Finset (Fin 5 → ZMod 3))
    (hcap : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = 0 → x = y) :
    A.card ≤ 45 := by
  sorry

end LefebvreVariations
