-- Prove2me | Theorems.Thm_LeblSCV_Varieties_germ_irreducible_decomposition
-- name    : LeblSCV.Varieties.germ_irreducible_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:16:14.139985+00:00
-- url     : https://prove2.me/theorems/7df96484-0317-4272-b465-e7d7bceb5881
-- title:
--   Proposition 6.7.3 — decomposition of a germ of a subvariety into irreducible germs
-- statement:
--   Let $p \in \mathbb{C}^n$ and let $(X, p)$ be a germ of a subvariety. Then there exist finitely many irreducible germs of subvarieties $(X_1, p), \dots, (X_k, p)$ such that
--   $$(X_1, p) \cup \cdots \cup (X_k, p) = (X, p)$$
--   and $(X_m, p) \not\subset (X_\ell, p)$ whenever $m \neq \ell$.
--
--   The $(X_\ell, p)$ are the irreducible components of the germ; the proposition is the geometric counterpart of the Noetherian property of $\mathcal{O}_p$.
--
--   **Formalization Note.** The germs are indexed by `Fin k`; the union of germs is the germ of the union of representatives. Irreducibility is Definition 6.7.1 as stated on the page (`IsIrreducibleGerm`).
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 194, Proposition 6.7.3

import Mathlib
import Definitions.Def_LeblSCV_Varieties_IsSubvarietyGerm
import Definitions.Def_LeblSCV_Varieties_IsIrreducibleGerm
import Definitions.Def_LeblSCV_Varieties_GermEq
import Definitions.Def_LeblSCV_Varieties_GermSubset

namespace LeblSCV.Varieties

/-- Lebl, Proposition 6.7.3: every germ `(X, p)` of a subvariety is a finite union
`(X₁, p) ∪ ⋯ ∪ (X_k, p)` of irreducible germs of subvarieties with `(X_m, p) ⊄ (X_ℓ, p)` whenever
`m ≠ ℓ`. -/
theorem germ_irreducible_decomposition {n : ℕ} (p : Fin n → ℂ) (X : Set (Fin n → ℂ))
    (hX : IsSubvarietyGerm p X) :
    ∃ (k : ℕ) (Xs : Fin k → Set (Fin n → ℂ)),
      (∀ ℓ, IsIrreducibleGerm p (Xs ℓ)) ∧ GermEq p (⋃ ℓ, Xs ℓ) X ∧
        ∀ m ℓ, m ≠ ℓ → ¬ GermSubset p (Xs m) (Xs ℓ) := by sorry

end LeblSCV.Varieties
