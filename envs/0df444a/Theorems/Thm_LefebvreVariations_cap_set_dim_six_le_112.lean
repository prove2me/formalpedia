-- Prove2me | Theorems.Thm_LefebvreVariations_cap_set_dim_six_le_112
-- name    : LefebvreVariations.cap_set_dim_six_le_112
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:02:21.255948+00:00
-- url     : https://prove2.me/theorems/ec7e7c37-c2c0-5f20-93ee-8f2faff8f248
-- title:
--   Lefebvre's variations, No. 110 — on a theme by Jordan Ellenberg and Dion Gijswijt: cap sets in F_3^6 have at most 112 points
-- statement:
--   Let $A\subseteq\mathbb{F}_3^{6}$ contain no three distinct points $x,y,z$ with $x+y+z=0$ (a cap set, equivalently a set with no three-term arithmetic progression). Then
--   $$
--   |A|\le 112.
--   $$
--   This is sharp: the maximum size of a cap set in $\mathbb{F}_3^{6}$ is exactly $112$.
--
--   **Formalization Note** The hypothesis is the one of the platform's `cap_set_bound`: for all $x,y,z\in A$, $x+y+z=0$ implies $x=y$ (in characteristic $3$ this forces $x=y=z$). The ambient space is `Fin 6 → ZMod 3` and the conclusion is the natural-number inequality `A.card ≤ 112`.
--
--   **Why this is a variation.** A variation on the platform's open `cap_set_bound` (|A| <= 2.756^n for cap sets in F_3^n). It fixes the dimension n = 6 and states the exact maximum size, which is a sharper finite fact than the asymptotic bound. The parent, whose true growth rate is unknown, remains open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   The maximum size of a cap set in AG(6,3) is 112: A. Potechin, Maximal caps in AG(6,3), Designs, Codes and Cryptography 46 (2008) (title, journal, volume and year verified by web search; pages not), also stated in the Bierbrauer-Edel survey on caps. The sequence of maximal cap sizes 2, 4, 9, 20, 45, 112 for dimensions 1 to 6 is tabulated in Follett, Kalail, McMahon, Pelland, Won, Partitions of AG(4,3) into maximal caps, arXiv:1302.4703 (verified by web search). Parent: the cap set bound of Ellenberg and Gijswijt, Annals of Math. 185 (2017), on the platform as `cap_set_bound`; pages not verified.

import Mathlib

namespace LefebvreVariations

/-- A cap set in `F_3^6` has at most `112` points (exact maximum 112). Source: A. Potechin, Maximal caps in AG(6,3), Des. Codes Cryptogr. 46 (2008) 243-259 (the maximum is 112) (cited from memory). -/
theorem cap_set_dim_six_le_112
    (A : Finset (Fin 6 → ZMod 3))
    (hcap : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = 0 → x = y) :
    A.card ≤ 112 := by
  sorry

end LefebvreVariations
