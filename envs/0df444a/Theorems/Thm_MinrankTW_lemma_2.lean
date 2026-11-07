-- Prove2me | Theorems.Thm_MinrankTW_lemma_2
-- name    : MinrankTW.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:12.103577+00:00
-- url     : https://prove2.me/theorems/3427c8ac-a8a8-45d1-9c9b-212966919d16
-- title:
--   Lemma 2 — the transform $T$ is invertible and turns a join into additive convolution of forms (20)
-- statement:
--   Let tables on the linear relations in $\mathbb F_q^a\oplus\mathbb F_q^c$ take values in a commutative ring, and let
--   $$
--   (Tf)(D,L,\beta)=\sum_{E\supseteq D,\ F\supseteq L}\ \sum_{\gamma:\ \gamma|_{D\times L}=\beta} f(E,F,\gamma)
--   $$
--   be the transform (19), where a relation is identified with its triple (16). Then $T$ is invertible, and if $h(R)=\sum_{R_1\boxplus R_2=R}f(R_1)g(R_2)$ then
--   $$
--   (Th)(D,L,\beta)=\sum_{\beta_1+\beta_2=\beta}(Tf)(D,L,\beta_1)\,(Tg)(D,L,\beta_2),
--   $$
--   the sum ranging over pairs of bilinear forms on $D\times L$.
--
--   After the transform the join is, for each fixed $(D,L)$, an ordinary additive convolution on the entries of the forms.
--
--   **Formalization Note** Tables are indexed by relations; the entry at $(D,L,\beta)$ is the entry at the relation defined by (17).
--
--   Differences from the source:
--   - reading: tables (their value ring unspecified in the lemma) → tables with values in an arbitrary commutative ring; reason: the lemma is used over polynomial rings and over the ring A of §A.3; its statement involves only ring operations
--   - encoding: tables indexed by triples (D, L, β) → tables indexed by linear relations, the triple's entry read at the relation (17); reason: (16) is a bijection; same tables
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Lemma 2, p.13, Eqs. (19)–(20)

import Mathlib
import Definitions.Def_MinrankTW_RelTriple
import Definitions.Def_MinrankTW_joinConv
import Definitions.Def_MinrankTW_tableMap
import Definitions.Def_MinrankTW_relTransforms

namespace MinrankTW

/-- **Lemma 2** (Transforming a join), Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), p.13, with Eq. (19). Tables take values in a
commutative ring. The transform `T` of (19), `(T f)(D, L, β) = ∑_{E ⊇ D, F ⊇ L}
∑_{γ|_{D×L} = β} f(E, F, γ)`, is invertible, and if `h(R) = ∑_{R₁ ⊞ R₂ = R} f(R₁) g(R₂)` then
`(T h)(D, L, β) = ∑_{β₁ + β₂ = β} (T f)(D, L, β₁) (T g)(D, L, β₂)` (20).

**Formalization Note** Tables are indexed by linear relations; `T` is `tableMap tKer` and the
entry at `(D, L, β)` is the entry at the relation `tripleToRel ⟨D, L, β⟩` (17). The sum in (20)
ranges over pairs of bilinear forms on `D × L`. -/
theorem lemma_2 {F : Type} [Field F] [Fintype F] {α γ : Type} [Fintype α] [Fintype γ]
    {A : Type} [CommRing A] :
    Function.Bijective (tableMap (tKer (F := F) (α := α) (γ := γ)) :
      (Submodule F ((α → F) × (γ → F)) → A) → Submodule F ((α → F) × (γ → F)) → A) ∧
    ∀ (f g : Submodule F ((α → F) × (γ → F)) → A) (T : RelTriple F α γ),
      tableMap tKer (joinConv f g) (tripleToRel T) =
        ∑ᶠ (β₁ : T.D →ₗ[F] T.L →ₗ[F] F) (β₂ : T.D →ₗ[F] T.L →ₗ[F] F) (_ : β₁ + β₂ = T.β),
          tableMap tKer f (tripleToRel ⟨T.D, T.L, β₁⟩) *
            tableMap tKer g (tripleToRel ⟨T.D, T.L, β₂⟩) := by sorry

end MinrankTW
