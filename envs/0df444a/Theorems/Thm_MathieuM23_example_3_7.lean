-- Prove2me | Theorems.Thm_MathieuM23_example_3_7
-- name    : MathieuM23.example_3_7
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-05T00:39:40.615762+00:00
-- url     : https://prove2.me/theorems/357eb7d1-7c51-4bdc-a6ae-9f4fd1c3c27a
-- title:
--   Example 3.7 — an explicit $M_{23}$-polynomial unramified outside $\{2,7,23\}$
-- statement:
--   Let $f=f_{3.7}\in\mathbb{Q}[x]$ be the degree-23 polynomial of Example 3.7 and let $K$ be a splitting field of $f$ over $\mathbb{Q}$. Then $K/\mathbb{Q}$ is Galois, $\mathrm{Gal}(K/\mathbb{Q})\cong M_{23}$, and $K$ is unramified outside $\{2,7,23\}$:
--
--   $$\mathrm{Gal}(K/\mathbb{Q})\cong M_{23},\qquad p\mid d_K\ \Rightarrow\ p\in\{2,7,23\}.$$
--
--   **Formalization Note** As in Example 1.2: the statement covers every number field that is a splitting field of $f$, and ramification is encoded through the absolute discriminant.
-- source:
--   X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, S. Zhang, *The Mathieu group M23 is a Galois group over Q*, arXiv:2608.08538v1 (2026), https://arxiv.org/abs/2608.08538, p. 7, Example 3.7

import Definitions.Def_MathieuM23_Group
import Definitions.Def_MathieuM23_Polynomials

namespace MathieuM23

theorem example_3_7 (K : Type) [Field K] [NumberField K]
    [Polynomial.IsSplittingField ℚ K fEx37] :
    IsGalois ℚ K ∧ Nonempty ((K ≃ₐ[ℚ] K) ≃* M23) ∧
      ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr K → p = 2 ∨ p = 7 ∨ p = 23 := by sorry

end MathieuM23
