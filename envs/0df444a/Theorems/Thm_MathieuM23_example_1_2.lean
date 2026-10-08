-- Prove2me | Theorems.Thm_MathieuM23_example_1_2
-- name    : MathieuM23.example_1_2
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-04T16:47:07.794985+00:00
-- url     : https://prove2.me/theorems/18d3ae8a-3c79-4826-9b09-53661cb1a6a1
-- title:
--   Example 1.2 — an explicit $M_{23}$-polynomial unramified outside $\{2,3,23\}$
-- statement:
--   Let $f=f_{1.2}\in\mathbb{Q}[x]$ be the degree-23 polynomial of Example 1.2 and let $K$ be a splitting field of $f$ over $\mathbb{Q}$. Then:
--
--   1. $K/\mathbb{Q}$ is Galois;
--   2. $\mathrm{Gal}(K/\mathbb{Q})\cong M_{23}$;
--   3. $K$ is unramified outside $\{2,3,23\}$: every prime $p$ dividing the discriminant $d_K$ belongs to $\{2,3,23\}$.
--
--   $$\mathrm{Gal}(K/\mathbb{Q})\cong M_{23},\qquad p\mid d_K\ \Rightarrow\ p\in\{2,3,23\}.$$
--
--   A formal proof gives an explicit, independently checkable witness of Theorem 1.1.
--
--   **Formalization Note** The statement is made for every number field $K$ that is a splitting field of $f$, which does not lose generality because splitting fields are unique up to isomorphism. "Unramified outside $S$" is encoded through the absolute discriminant, which is equivalent by Dedekind's discriminant theorem.
-- source:
--   X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, S. Zhang, *The Mathieu group M23 is a Galois group over Q*, arXiv:2608.08538v1 (2026), https://arxiv.org/abs/2608.08538, p. 1–2, Example 1.2

import Definitions.Def_MathieuM23_Group
import Definitions.Def_MathieuM23_Polynomials

namespace MathieuM23

theorem example_1_2 (K : Type) [Field K] [NumberField K]
    [Polynomial.IsSplittingField ℚ K fEx12] :
    IsGalois ℚ K ∧ Nonempty ((K ≃ₐ[ℚ] K) ≃* M23) ∧
      ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr K → p = 2 ∨ p = 3 ∨ p = 23 := by sorry

end MathieuM23
