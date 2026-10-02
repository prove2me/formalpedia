-- Prove2me | Theorems.Thm_MooreFoelner_exists_const_isFolnerSet_exists_towerExp_le_card_Rf
-- name    : MooreFoelner.exists_const_isFolnerSet_exists_towerExp_le_card_Rf
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T01:22:51.265832+00:00
-- url     : https://prove2.me/theorems/37ba9e78-4e3b-4997-ab2d-8d549b1f9cf1
-- title:
--   Claim 5.14 — a K^(−n)-Følner set of F contains an element with tower-size reduced diagram
-- statement:
--   There is a constant $K > 1$ such that every $K^{-n}$-Følner set $A \subseteq F$ (with respect to $\Gamma = \{x_0^{\pm1}, x_1^{\pm1}\}$) contains an element $f$ whose reduced tree diagram $(L_f, R_f)$ has at least $\exp_n(0)$ leaves in each tree.
--
--   **Formalization Note.** Moore writes "an element with a tree diagram", which every element has with arbitrarily many leaves; the proof bounds the reduced diagram $R_f$, which is what is stated.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 18, Claim 5.14

import Mathlib
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees
import Definitions.Def_ThompsonAmenability

namespace MooreFoelner

theorem exists_const_isFolnerSet_exists_towerExp_le_card_Rf :
    ∃ K : ℝ, 1 < K ∧ ∀ (n : ℕ) (A : Finset MooreF), IsFolnerSet gens A (K ^ (-(n : ℤ))) →
      ∃ f ∈ A, ThompsonAmenability.towerExp n 0 ≤ (Lf (toMap f)).card ∧
        ThompsonAmenability.towerExp n 0 ≤ (Rf (toMap f)).card := by
  sorry

end MooreFoelner
