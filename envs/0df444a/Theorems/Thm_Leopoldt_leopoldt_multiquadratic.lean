-- Prove2me | Theorems.Thm_Leopoldt_leopoldt_multiquadratic
-- name    : Leopoldt.leopoldt_multiquadratic
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:17:26.828357+00:00
-- url     : https://prove2.me/theorems/a2d4de74-3418-4266-90fa-89c1a676c568
-- title:
--   Leopoldt's conjecture for multiquadratic fields (Galois group of exponent 2)
-- statement:
--   Leopoldt's conjecture holds, at every prime $p$, for every number field $\mathbb{K}$ that is Galois over $\mathbb{Q}$ with Galois group of exponent dividing $2$, i.e. every element $\sigma \in G = \mathrm{Gal}(\mathbb{K}/\mathbb{Q})$ satisfies $\sigma^2 = 1$:
--
--   $$\mathcal{D}_L(\mathbb{K}) = 0 .$$
--
--   Equivalently, this covers all multiquadratic fields $\mathbb{K} = \mathbb{Q}(\sqrt{a_1}, \dots, \sqrt{a_k})$ with $a_i \in \mathbb{Q}^\times$ of arbitrary signs. Such a field is Galois, hence either totally real or totally imaginary. In the totally real case this is Leopoldt's conjecture for totally real multiquadratic fields. In the totally imaginary case $G$ is abelian, so $\mathbb{K}$ is a CM field whose maximal real subfield $\mathbb{K}^+$ is again Galois over $\mathbb{Q}$ with Galois group a quotient of $G$ (so still of exponent $2$) and totally real; since the Leopoldt defect of a CM field equals that of its maximal real subfield, the conjecture for $\mathbb{K}$ follows from that for $\mathbb{K}^+$.
--
--   **Formalization note.** No signature hypothesis is imposed; the hypotheses are `IsGalois ℚ K` and `∀ σ : K ≃ₐ[ℚ] K, σ * σ = 1`. Any prime $p$ is allowed.
-- source:
--   A. Brumer, On the units of algebraic number fields, Mathematika 14 (1967), 121-124 (Leopoldt's conjecture for abelian extensions of Q). For the elementary argument in the multiquadratic case (eigen-decomposition of the unit group under the characters of Gal(K/Q) = (Z/2)^k, with the units of the 2^k - 1 real quadratic subfields spanning a subgroup of finite index), see L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Section 5.5 (Leopoldt's conjecture, Theorem 5.29) and Section 8.1 (units of abelian fields: the character decomposition of the unit group); cf. H. Hasse, Über die Klassenzahl abelscher Zahlkörper (1952) for units of multiquadratic fields. The CM case reduces to the maximal real subfield via Washington, GTM 83, Proposition 5.33 / Section 5.5 (the Leopoldt defect of a CM field equals that of K^+, since E_K^+ has finite index in E_K).

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem leopoldt_multiquadratic (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (hG : ∀ σ : K ≃ₐ[ℚ] K, σ * σ = 1) :
    LeopoldtConjecture p K := by sorry
end Leopoldt
