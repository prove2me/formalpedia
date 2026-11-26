-- Prove2me | Theorems.Thm_LefebvreVariations_cap_set_dim_four_le_twenty
-- name    : LefebvreVariations.cap_set_dim_four_le_twenty
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:01:49.978305+00:00
-- url     : https://prove2.me/theorems/0bd7907f-5bcf-4045-9305-ea272049ef56
-- title:
--   Lefebvre's variations, No. 108 — on a theme by Jordan Ellenberg and Dion Gijswijt: cap sets in F_3^4 have at most twenty points
-- statement:
--   Let $A\subseteq\mathbb{F}_3^{4}$ contain no three distinct points $x,y,z$ with $x+y+z=0$ (a cap set, equivalently a set with no three-term arithmetic progression). Then
--   $$
--   |A|\le 20.
--   $$
--   This is sharp: the maximum size of a cap set in $\mathbb{F}_3^{4}$ is exactly $20$.
--
--   **Formalization Note** The hypothesis is the one of the platform's `cap_set_bound`: for all $x,y,z\in A$, $x+y+z=0$ implies $x=y$ (in characteristic $3$ this forces $x=y=z$). The ambient space is `Fin 4 → ZMod 3` and the conclusion is the natural-number inequality `A.card ≤ 20`.
--
--   **Why this is a variation.** A variation on the platform's open `cap_set_bound` (|A| <= 2.756^n for cap sets in F_3^n). It fixes the dimension n = 4 and states the exact maximum size, which is a sharper finite fact than the asymptotic bound. The parent, whose true growth rate is unknown, remains open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   The maximum size of a cap set in AG(4,3) is 20: verified here by an exhaustive computer search (a cap of size 20 exists, none of size 21). The sequence of maximal cap sizes 2, 4, 9, 20, 45, 112 for dimensions 1 to 6 is tabulated in Follett, Kalail, McMahon, Pelland, Won, Partitions of AG(4,3) into maximal caps, arXiv:1302.4703 (verified by web search). Attributed to Pellegrino (1970), cited from memory, not verified. Parent: the cap set bound of Ellenberg and Gijswijt, Annals of Math. 185 (2017), on the platform as `cap_set_bound`; pages not verified.

import Mathlib

namespace LefebvreVariations

/-- A cap set in `F_3^4` has at most `20` points (exact maximum 20). Source: R. Pellegrino, Sulle calotte massime dello spazio affine AG(4,3), 1970 (the maximum is 20) (cited from memory). -/
theorem cap_set_dim_four_le_twenty
    (A : Finset (Fin 4 → ZMod 3))
    (hcap : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = 0 → x = y) :
    A.card ≤ 20 := by
  sorry

end LefebvreVariations
