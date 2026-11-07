-- Prove2me | Theorems.Thm_MinrankTW_eq_16_18
-- name    : MinrankTW.eq_16_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:04.250198+00:00
-- url     : https://prove2.me/theorems/d43314d4-9edd-47d3-a255-2227ea56a02e
-- title:
--   Eqs. (16)–(18) — linear relations as triples $(D,L,\beta)$, and the join of triples
-- statement:
--   Let $R\le\mathbb F_q^a\oplus\mathbb F_q^c$ be a linear relation.
--
--   1. (16) With $D=\mathrm{dom}\,R$ and $L=\{\lambda\in\mathbb F_q^{1\times c}:\lambda y=0\ \text{for all}\ y\in R(0)\}$, the value $\beta(x,\lambda)=\lambda y$ for $(x,y)\in R$, $\lambda\in L$ is independent of the chosen $y$ and defines a bilinear form on $D\times L$.
--   2. (17) $R=\{(x,y) : x\in D,\ \lambda y=\beta(x,\lambda)\ \text{for all}\ \lambda\in L\}$.
--   3. Conversely every triple $(D,L,\beta)$ — a subspace $D\le\mathbb F_q^a$, a subspace $L$ of row vectors and a bilinear form on $D\times L$ — is the triple (16) of the relation it defines by (17); so (16) is a bijection between linear relations and triples.
--   4. (18) If $R_1,R_2$ have triples $(D_1,L_1,\beta_1),(D_2,L_2,\beta_2)$, then $R_1\boxplus R_2$ has the triple $(D_1\cap D_2,\ L_1\cap L_2,\ \beta_1+\beta_2)$, both forms restricted to the common spaces.
--
--   In these coordinates the join restricts and adds bilinear forms, which Lemma 2 turns into an additive convolution.
--
--   **Formalization Note** Row vectors $\lambda$ are functions on the row index set acting by the dot product.
--
--   Differences from the source:
--   - encoding: row vectors λ ∈ F^{1×c} → functions γ → F acting on y by the dot product; reason: Lean convention; same objects
--   - encoding: "(16) represents every linear relation uniquely" → existence of the triple, (17), every triple represents its relation, and bijectivity of the map (17); reason: the bijection spelled out; same content
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 4.1, pp.12–13, Eqs. (16)–(18)

import Mathlib
import Definitions.Def_MinrankTW_relJoin
import Definitions.Def_MinrankTW_RelTriple

namespace MinrankTW

/-- **Eqs. (16)–(18)** (Linear measurements), Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §4.1, pp.12–13.
1. (16) Every linear relation `R ≤ F^a ⊕ F^c` has a triple `(D, L, β)`: `D = dom R`,
   `L = {λ : λy = 0 on R(0)}`, and `β(x, λ) = λy` for `(x, y) ∈ R` is a well-defined bilinear
   form on `D × L`.
2. (17) `R = {(x, y) : x ∈ D, λy = β(x, λ) for all λ ∈ L}`.
3. Every triple `(D, L, β)` is the triple of the relation (17) it defines, so (16) represents
   linear relations bijectively by triples.
4. (18) `(D₁, L₁, β₁) ⊞ (D₂, L₂, β₂) = (D₁ ∩ D₂, L₁ ∩ L₂, β₁ + β₂)`, both forms restricted to
   the common spaces.

**Formalization Note** Row vectors are `γ → F` acting by `dotProduct`; `Represents R T` is
"`T` is the triple (16) of `R`" and `tripleToRel` is (17). -/
theorem eq_16_18 {F : Type} [Field F] [Fintype F] {α γ : Type} [Fintype α] [Fintype γ] :
    (∀ R : Submodule F ((α → F) × (γ → F)), ∃ T : RelTriple F α γ, Represents R T) ∧
    (∀ (R : Submodule F ((α → F) × (γ → F))) (T : RelTriple F α γ),
      Represents R T → tripleToRel T = R) ∧
    (∀ T : RelTriple F α γ, Represents (tripleToRel T) T) ∧
    Function.Bijective (tripleToRel : RelTriple F α γ → Submodule F ((α → F) × (γ → F))) ∧
    (∀ (R₁ R₂ : Submodule F ((α → F) × (γ → F))) (T₁ T₂ T : RelTriple F α γ),
      Represents R₁ T₁ → Represents R₂ T₂ → Represents (relJoin R₁ R₂) T →
      T.D = T₁.D ⊓ T₂.D ∧ T.L = T₁.L ⊓ T₂.L ∧
      ∀ (x : α → F) (l : γ → F) (hx : x ∈ T.D) (hx₁ : x ∈ T₁.D) (hx₂ : x ∈ T₂.D)
        (hl : l ∈ T.L) (hl₁ : l ∈ T₁.L) (hl₂ : l ∈ T₂.L),
        T.β ⟨x, hx⟩ ⟨l, hl⟩ = T₁.β ⟨x, hx₁⟩ ⟨l, hl₁⟩ + T₂.β ⟨x, hx₂⟩ ⟨l, hl₂⟩) := by sorry

end MinrankTW
