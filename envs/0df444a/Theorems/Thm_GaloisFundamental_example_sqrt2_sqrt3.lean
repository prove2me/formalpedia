-- Prove2me | Theorems.Thm_GaloisFundamental_example_sqrt2_sqrt3
-- name    : GaloisFundamental.example_sqrt2_sqrt3
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T01:02:55.561353+00:00
-- url     : https://prove2.me/theorems/db388c04-66f1-457f-bcbd-f18aaabfca9e
-- title:
--   Example 1: $\mathbb{Q}(\sqrt2,\sqrt3)$ has Klein four Galois group and five intermediate fields
-- statement:
--   Let $K = \mathbb{Q}(\sqrt2, \sqrt3) \subseteq \mathbb{R}$. Then
--
--   - $[K : \mathbb{Q}] = 4$;
--   - $K/\mathbb{Q}$ is Galois;
--   - $\operatorname{Gal}(K/\mathbb{Q})$ is a Klein four-group;
--   - $\operatorname{Gal}(K/\mathbb{Q})$ has exactly $5$ subgroups, and $K/\mathbb{Q}$ has exactly $5$ intermediate fields.
-- source:
--   Wikipedia, "Fundamental theorem of Galois theory", revision oldid=1345286594, https://en.wikipedia.org/w/index.php?title=Fundamental_theorem_of_Galois_theory&oldid=1345286594, section "Example 1" (Galois group of Q(√2, √3) is the Klein four-group; its five subgroups correspond to the five intermediate fields)

import Mathlib

namespace GaloisFundamental

theorem example_sqrt2_sqrt3 :
    Module.finrank ℚ (IntermediateField.adjoin ℚ ({√2, √3} : Set ℝ)) = 4 ∧
      IsGalois ℚ (IntermediateField.adjoin ℚ ({√2, √3} : Set ℝ)) ∧
      IsKleinFour (IntermediateField.adjoin ℚ ({√2, √3} : Set ℝ) ≃ₐ[ℚ]
        IntermediateField.adjoin ℚ ({√2, √3} : Set ℝ)) ∧
      Nat.card (Subgroup (IntermediateField.adjoin ℚ ({√2, √3} : Set ℝ) ≃ₐ[ℚ]
        IntermediateField.adjoin ℚ ({√2, √3} : Set ℝ))) = 5 ∧
      Nat.card (IntermediateField ℚ (IntermediateField.adjoin ℚ ({√2, √3} : Set ℝ))) = 5 := by
  sorry

end GaloisFundamental
