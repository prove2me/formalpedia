-- Prove2me | Theorems.Thm_LefebvreVariations_cap_set_dim_three_le_nine
-- name    : LefebvreVariations.cap_set_dim_three_le_nine
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:01:28.718779+00:00
-- url     : https://prove2.me/theorems/e6ae806e-71d0-5de5-93a7-e91a36173b2e
-- title:
--   Lefebvre's variations, No. 128 — on a theme by Jordan Ellenberg and Dion Gijswijt: cap sets in F_3^3 have at most nine points
-- statement:
--   Let $A\subseteq\mathbb{F}_3^{3}$ contain no three distinct points $x,y,z$ with $x+y+z=0$ (a cap set, equivalently a set with no three-term arithmetic progression). Then
--   $$
--   |A|\le 9.
--   $$
--   This is sharp: the maximum size of a cap set in $\mathbb{F}_3^{3}$ is exactly $9$.
--
--   **Formalization Note** The hypothesis is the one of the platform's `cap_set_bound`: for all $x,y,z\in A$, $x+y+z=0$ implies $x=y$ (in characteristic $3$ this forces $x=y=z$). The ambient space is `Fin 3 → ZMod 3` and the conclusion is the natural-number inequality `A.card ≤ 9`.
--
--   **Why this is a variation.** A variation on the platform's open `cap_set_bound` (|A| <= 2.756^n for cap sets in F_3^n). It fixes the dimension n = 3 and states the exact maximum size, which is a sharper finite fact than the asymptotic bound. The parent, whose true growth rate is unknown, remains open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   The maximum size of a cap set in AG(3,3) is 9: verified here by an exhaustive computer search (a cap of size 9 exists, none of size 10). The sequence of maximal cap sizes 2, 4, 9, 20, 45, 112 for dimensions 1 to 6 is tabulated in Follett, Kalail, McMahon, Pelland, Won, Partitions of AG(4,3) into maximal caps, arXiv:1302.4703 (verified by web search). Original attribution not verified (classical). Parent: the cap set bound of Ellenberg and Gijswijt, Annals of Math. 185 (2017), on the platform as `cap_set_bound`; pages not verified.

import Mathlib

namespace LefebvreVariations

/-- A cap set in `F_3^3` has at most `9` points (exact maximum 9). Source: the maximal caps in AG(3,3) have 9 points (classical, see e.g. Hill, Caps and codes, Discrete Math. 22 (1978)) (cited from memory). -/
theorem cap_set_dim_three_le_nine
    (A : Finset (Fin 3 → ZMod 3))
    (hcap : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = 0 → x = y) :
    A.card ≤ 9 := by
  sorry

end LefebvreVariations
