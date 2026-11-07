-- Prove2me | Theorems.Thm_NoPerfectRandComp_lemma_4_5
-- name    : NoPerfectRandComp.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:46:01.437267+00:00
-- url     : https://prove2.me/theorems/9f96dbba-f45d-40d2-ba87-ed03e3ace2ff
-- title:
--   Lemma 4.5 — a linear encoding with private marginals
-- statement:
--   For every integer $a \ge 1$:
--   1. there is a surjective linear map $H_a : \mathbb F_2^{36a} \to \mathbb F_2^{a}$ such that the uniform distributions on any two fibres of $H_a$ have identical marginals on any set of at most $12a$ input coordinates, and these marginals are uniform;
--   2. every nonempty finite alphabet $\Gamma$ of size at most $2^a$ has a total decoding from $36a$ bits with this property, for any chosen (distinct) representatives of its symbols in $\mathbb F_2^a$: a private cell encoding whose decoder maps each representative to its symbol.
--
--   This is what makes every statement about the encoded functions $W_q$ and $\hat M_q$ non-vacuous: admissible encodings exist at every payload length.
--
--   Differences from the source:
--   - encoding: identical and uniform marginals of fibres → the count identity of the private-map definition; reason: equal counts for every fibre and every pattern on J is the same property
--   - encoding: "a total decoding from 36a bits with this property for any chosen representatives" → a private cell encoding (private map plus surjective decoder) whose decoder maps each representative to its symbol; reason: same object
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Lemma 4.5, p.14

import Mathlib
import Definitions.Def_NoPerfectRandComp_Encoding

namespace NoPerfectRandComp

/-- Lemma 4.5 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.14 (a linear encoding with private marginals): for every integer
`a ≥ 1` there is a surjective linear map `H_a : 𝔽₂^{36a} → 𝔽₂^a` whose fibres have identical,
uniform marginals on every set of at most `12a` coordinates; and every nonempty finite alphabet of
size at most `2^a` has a total decoding from `36a` bits with this property, for any chosen
representatives of its symbols in `𝔽₂^a`.

**Formalization Note** "Total decoding with this property" is an `Encoding a Γ` (a private `H`
and a surjective decoder) whose decoder maps each chosen representative to its symbol. -/
theorem lemma_4_5 (a : ℕ) (ha : 1 ≤ a) :
    (∃ H : (Fin (36 * a) → ZMod 2) →ₗ[ZMod 2] (Fin a → ZMod 2), IsPrivateMap a H) ∧
    ∀ (Γ : Type) [Fintype Γ] [Nonempty Γ], Fintype.card Γ ≤ 2 ^ a →
      ∀ rep : Γ → (Fin a → ZMod 2), Function.Injective rep →
        ∃ enc : Encoding a Γ, ∀ σ, enc.dec (rep σ) = σ := by sorry

end NoPerfectRandComp
