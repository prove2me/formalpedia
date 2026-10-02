-- Prove2me | Theorems.Thm_LeblSCV_Varieties_hypervariety_germ_union_connected_regular
-- name    : LeblSCV.Varieties.hypervariety_germ_union_connected_regular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:15:25.378062+00:00
-- url     : https://prove2.me/theorems/4b8949b9-1f4e-40cf-8129-c82e48b198cd
-- title:
--   Corollary 6.6.3 — a hypervariety germ is a finite union of hypervarieties with connected regular parts
-- statement:
--   Let $U_0 \subset \mathbb{C}^n$ be open, let $X_0 \subset U_0$ be a subvariety of pure codimension $1$, and let $p \in U_0$. Then there exist an open neighborhood $U$ of $p$, a subvariety $X \subset U$ with $(X, p) = (X_0, p)$, and subvarieties $X_1, \dots, X_k \subset U$ of pure codimension $1$ such that $(X_\ell)_{\mathrm{reg}}$ is connected for every $\ell$ and
--   $$X = X_1 \cup \cdots \cup X_k .$$
--
--   This decomposes a hypervariety germ into pieces that, as later shown, are its irreducible components.
--
--   **Formalization Note.** The germ $(X_0,p)$ is given by a representative, as in Theorem 6.6.1. "Connected" is Mathlib's `IsConnected` (nonempty and connected); the number $k$ of pieces may be $0$, which is forced exactly when $(X_0,p)$ is the empty germ.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 189, Corollary 6.6.3

import Mathlib
import Definitions.Def_LeblSCV_Varieties_IsSubvariety
import Definitions.Def_LeblSCV_Varieties_IsPureCodim
import Definitions.Def_LeblSCV_Varieties_GermEq
import Definitions.Def_LeblSCV_Varieties_regularPoints

namespace LeblSCV.Varieties

/-- Lebl, Corollary 6.6.3: let `(X₀, p)` be the germ at `p` of a subvariety `X₀` of an open set
`U₀ ∋ p` of pure codimension 1. Then there are an open neighborhood `U` of `p`, a representative
`X ⊆ U` of `(X₀, p)` that is a subvariety of `U`, and subvarieties `X₁, …, X_k ⊆ U` of pure
codimension 1 with `(X_ℓ)_reg` connected for every `ℓ` and `X = X₁ ∪ ⋯ ∪ X_k`. -/
theorem hypervariety_germ_union_connected_regular {n : ℕ} {U₀ X₀ : Set (Fin n → ℂ)}
    (hX₀ : IsSubvariety U₀ X₀) (hpure : IsPureCodim X₀ 1) {p : Fin n → ℂ} (hp : p ∈ U₀) :
    ∃ U X : Set (Fin n → ℂ), IsOpen U ∧ p ∈ U ∧ IsSubvariety U X ∧ GermEq p X X₀ ∧
      ∃ (k : ℕ) (Xs : Fin k → Set (Fin n → ℂ)),
        (∀ ℓ, IsSubvariety U (Xs ℓ) ∧ IsPureCodim (Xs ℓ) 1 ∧ IsConnected (regularPoints (Xs ℓ))) ∧
          X = ⋃ ℓ, Xs ℓ := by sorry

end LeblSCV.Varieties
