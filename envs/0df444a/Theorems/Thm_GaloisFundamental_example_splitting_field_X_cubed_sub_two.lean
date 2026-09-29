-- Prove2me | Theorems.Thm_GaloisFundamental_example_splitting_field_X_cubed_sub_two
-- name    : GaloisFundamental.example_splitting_field_X_cubed_sub_two
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T01:08:23.447977+00:00
-- url     : https://prove2.me/theorems/964bb9ea-5644-4264-939f-9b7422a314f2
-- title:
--   Example 2: the splitting field of $x^3-2$ over $\mathbb{Q}$ has Galois group $S_3$
-- statement:
--   Let $K$ be the splitting field of $x^3 - 2$ over $\mathbb{Q}$. Then
--
--   - $[K : \mathbb{Q}] = 6$;
--   - $\operatorname{Gal}(x^3-2) = \operatorname{Gal}(K/\mathbb{Q})$ is isomorphic to the symmetric group $S_3$;
--   - $\operatorname{Gal}(K/\mathbb{Q})$ has exactly $6$ subgroups, and $K/\mathbb{Q}$ has exactly $6$ intermediate fields.
-- source:
--   Wikipedia, "Fundamental theorem of Galois theory", revision oldid=1345286594, https://en.wikipedia.org/w/index.php?title=Fundamental_theorem_of_Galois_theory&oldid=1345286594, section "Example 2" (splitting field of x^3 − 2 over Q; degree 6; Galois group isomorphic to the symmetric group on three letters; its subgroups and corresponding subfields)

import Mathlib
open Polynomial

namespace GaloisFundamental

theorem example_splitting_field_X_cubed_sub_two :
    Module.finrank ℚ (X ^ 3 - C 2 : ℚ[X]).SplittingField = 6 ∧
      Nonempty ((X ^ 3 - C 2 : ℚ[X]).Gal ≃* Equiv.Perm (Fin 3)) ∧
      Nat.card (Subgroup (X ^ 3 - C 2 : ℚ[X]).Gal) = 6 ∧
      Nat.card (IntermediateField ℚ (X ^ 3 - C 2 : ℚ[X]).SplittingField) = 6 := by
  sorry

end GaloisFundamental
