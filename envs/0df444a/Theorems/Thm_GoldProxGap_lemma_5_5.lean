-- Prove2me | Theorems.Thm_GoldProxGap_lemma_5_5
-- name    : GoldProxGap.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:23:44.389213+00:00
-- url     : https://prove2.me/theorems/0e4b7f0f-1d7d-4306-a219-4e221e0c6f49
-- title:
--   Lemma 5.5 — labels of linear functions: $\ell_\omega^2+\ell_\omega=\omega^2\Lambda$, the label space is a binary $d$-space, and $\deg\ell_\omega=N/2$ with leading coefficient $\eta\omega$
-- statement:
--   **Lemma 5.5 (Labels of linear functions).** Let $D\subseteq\mathbb B$ be binary additive of dimension $d$, $N=2^d$. Every $\mathbb F_2$-linear function $\varphi:D\to\mathbb F_2$ agrees on $D$ with exactly one polynomial $\ell\in\mathbb B[X]$ that is a combination of $X,X^2,X^4,\dots,X^{N/2}$. The coefficient of $X$ in $\ell$ has a square root $\omega\in\mathbb B$, the label of $\varphi$; write $\ell_\omega=\ell$.
--   1. $\ell_\omega^2+\ell_\omega=\omega^2\Lambda$.
--   2. The labels form a binary $d$-space $\hat D\subseteq\mathbb B$, the label space of $D$, and $\omega\mapsto\ell_\omega|_D$ is an $\mathbb F_2$-linear bijection from $\hat D$ onto the linear functions $D\to\mathbb F_2$.
--   3. For $\omega\ne0$, $\ell_\omega$ has degree $N/2$ and leading coefficient $\eta\omega$.
--
--   The labels give binary coordinates on $D$ together with polynomials representing them, from which the polynomials of quadratic functions are built.
--
--   **Formalization Note** $\ell_\varphi$ is defined as the canonical representative of $\varphi$ (degree $<N$); the lemma asserts that it is a combination of $X^{2^i}$, $i<d$, and the only such combination agreeing with $\varphi$. Part 2 is stated as: the set of labels is an additive subgroup with $2^d$ elements, and the label map is injective and additive.
--
--   Differences from the source:
--   - encoding: the unique combination ℓ of X, …, X^{N/2} agreeing with φ → ℓ_φ defined as the canonical representative of φ, with conclusions that it is such a combination, agrees with φ, and is the only such combination; reason: the uniqueness makes the two the same polynomial
--   - encoding: ω ↦ ℓ_ω|_D is an F₂-linear bijection from D̂ onto the linear functions → φ ↦ label(φ) is injective and additive, and D̂ is its range; reason: the inverse of an additive bijection is an additive bijection
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), Lemma 5.5, pp.37–38

import Mathlib
import Definitions.Def_GoldProxGap_label

open Polynomial

open scoped Classical

namespace GoldProxGap

/-- **Lemma 5.5 (Labels of linear functions)**, pp.37–38. Dao, Kominers, Thaler, Zheng,
*Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*, STOC 2027 submission
manuscript (2 November 2026, sha256 6c2d9ced…). Setting of §5.3 (p.37): `D ⊆ B` is binary
additive of dimension `d`, `N = 2^d`, `B` a finite field of characteristic two.

"Every F₂-linear function φ : D → F₂ agrees on D with exactly one polynomial ℓ ∈ B[X] that is a
combination of X, X², X⁴, …, X^{N/2}. The coefficient of X in ℓ has a square root ω ∈ B. We call
ω the label of φ and write ℓ_ω for ℓ.
1. The polynomial ℓ_ω satisfies ℓ_ω² + ℓ_ω = ω²Λ.
2. The labels form a binary d-space D̂ ⊆ B, the label space of D. The map ω ↦ ℓ_ω|_D is an
F₂-linear bijection from D̂ onto the space of linear functions D → F₂.
3. For ω ≠ 0, the polynomial ℓ_ω has degree N/2 and leading coefficient ηω."

**Formalization Note.** `ℓ_φ = ellPoly D φ` is defined as the canonical representative
(Definition 3.6) of `φ`; the first clauses say that it is a combination of `X^{2^i}`, `i < d`,
agrees with `φ` on `D`, and is the only such combination. `ω = label D φ` (square root of the
`X`-coefficient), `Λ = normLocator D`, `η = eta D`. Part 2 is stated as: the label space is the
carrier of an additive subgroup with `2^d` elements, and `φ ↦ label D φ` is injective and additive
(so its inverse `ω ↦ ℓ_ω|_D` is an `F₂`-linear bijection from `D̂` onto the linear functions). -/
theorem lemma_5_5 {B : Type} [Field B] [Fintype B] [CharP B 2] (D : AddSubgroup B) (d : ℕ)
    (hD : Nat.card D = 2 ^ d) :
    (∀ φ : D →+ ZMod 2,
      (∃ c : Fin d → B, ellPoly D φ = ∑ i : Fin d, C (c i) * X ^ (2 ^ (i : ℕ))) ∧
      (∀ x : D, (ellPoly D φ).eval (x : B) = ((φ x).val : B)) ∧
      (∀ ℓ : B[X], (∃ c : Fin d → B, ℓ = ∑ i : Fin d, C (c i) * X ^ (2 ^ (i : ℕ))) →
        (∀ x : D, ℓ.eval (x : B) = ((φ x).val : B)) → ℓ = ellPoly D φ) ∧
      label D φ ^ 2 = (ellPoly D φ).coeff 1 ∧
      (ellPoly D φ) ^ 2 + ellPoly D φ = C (label D φ ^ 2) * normLocator D ∧
      (label D φ ≠ 0 → (ellPoly D φ).natDegree = 2 ^ d / 2 ∧
        (ellPoly D φ).leadingCoeff = eta D * label D φ)) ∧
    (∃ W : AddSubgroup B, (W : Set B) = labelSpace D ∧ Nat.card W = 2 ^ d) ∧
    Function.Injective (label D) ∧
    (∀ φ φ' : D →+ ZMod 2, label D (φ + φ') = label D φ + label D φ') := by sorry

end GoldProxGap
