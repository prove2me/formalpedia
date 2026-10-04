-- Prove2me | Theorems.Thm_GaloisFundamental_example_real_cube_root_two_not_galois
-- name    : GaloisFundamental.example_real_cube_root_two_not_galois
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T01:09:33.349979+00:00
-- url     : https://prove2.me/theorems/db51ea49-7829-428a-9884-368e3c644649
-- title:
--   Example 4: $\mathbb{Q}(\sqrt[3]{2})/\mathbb{Q}$ is not Galois
-- statement:
--   Let $\theta = \sqrt[3]{2}$ be the real cube root of $2$ and $K = \mathbb{Q}(\theta) \subseteq \mathbb{R}$. Then $[K : \mathbb{Q}] = 3$, the automorphism group $\operatorname{Aut}(K/\mathbb{Q})$ is trivial, and $K/\mathbb{Q}$ is not Galois. (So the Galois correspondence fails for this finite extension.)
-- source:
--   Wikipedia, "Fundamental theorem of Galois theory", revision oldid=1345286594, https://en.wikipedia.org/w/index.php?title=Fundamental_theorem_of_Galois_theory&oldid=1345286594, section "Example 4" (a finite extension which is not Galois; Aut(E/F) is trivial, and the Galois correspondence fails)

import Mathlib

namespace GaloisFundamental

theorem example_real_cube_root_two_not_galois :
    Module.finrank ℚ (IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ)) = 3 ∧
      Nat.card (IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ) ≃ₐ[ℚ]
        IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ)) = 1 ∧
      ¬ IsGalois ℚ (IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ)) := by
  sorry

end GaloisFundamental
