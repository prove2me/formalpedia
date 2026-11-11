-- Prove2me | Theorems.Thm_GoldProxGap_lemma_5_12
-- name    : GoldProxGap.lemma_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:24:59.809721+00:00
-- url     : https://prove2.me/theorems/d6e10f3c-60d4-4cc8-a5c3-e68d635f049a
-- title:
--   Lemma 5.12 — Gold moments give $2^{2t}$ distinct monic polynomials $P=R+C$ with $T$ roots on $D$ and $P'(P^2+L_D)=\lambda_0P$
-- statement:
--   **Lemma 5.12 (Gold moments give polynomials with many roots).** Let $D\subseteq\mathbb B$ be binary additive of dimension $d$, $N=2^d$, fix a basis $\omega_1,\dots,\omega_d$ of the label space, let $2\le t\le d/2$, and put
--   $$
--   T=\frac N2-\frac N{2^{t+1}},\qquad R=\sqrt{L_D-\lambda_0X}.
--   $$
--   Each alternating binary $d\times d$ matrix $A$ of rank $2t$ with $M_1(A)=\dots=M_{t-1}(A)=0$ gives $2^{2t}$ distinct monic polynomials $P=R+C\in\mathbb B[X]$ with $\deg C=T/2$, one for each label $\omega$ for which $\psi$ vanishes on the polar radical of $A$ (Lemma 5.10). The roots of $P$ on $D$ are the $T$ points where $\psi+\kappa$ takes the value one. Polynomials from different matrices are also distinct. Every polynomial $P$ of the family satisfies:
--   1. $P'(P^2+L_D)=\lambda_0P$;
--   2. its set of roots on $D$ is a union of cosets of a subspace of $D$ of dimension $d-2t$;
--   3. it takes the same value as any other member of the family at most at $N/2^{2t}$ points outside $D$, in any field containing $\mathbb B$.
--
--   These polynomials, all sharing the high part $R$, are the input of the pole reduction (Lemma 3.11) in the proof of Theorem 5.1; property 3 bounds the collisions that Lemma 3.19 averages over.
--
--   **Formalization Note** The family is a function $P$ on pairs $(A,\varphi)$ of a matrix and the linear function of a label, injective on the admissible pairs. The level $\kappa$ is existential (Lemma 5.10 makes it unique). Property 2 says that the roots on $D$ are invariant under translation by an additive subgroup $W\le D$ with $2^{d-2t}$ elements. Property 3 counts, in every field $\mathbb F'$ with an algebra map from $\mathbb B$, the roots outside $D$ of the difference of two members.
--
--   Differences from the source:
--   - encoding: a basis ω₁, …, ω_d of the label space D̂ → a coordinate basis φs of the linear functions D → F₂ with ω_i = label(φs i); reason: by Lemma 5.5(2) the label map is an F₂-linear bijection, so this is the same data
--   - encoding: 2^{2t} distinct polynomials for each A, one for each label of Lemma 5.10, distinct across matrices → a function P on admissible pairs (A, φ), injective on them; reason: the same family, indexed by its pairs
--   - encoding: the T points where ψ + κ takes the value one (κ of Lemma 5.10) → some κ with |{ψ + κ = 1}| = T, and the roots of P on D are exactly {ψ + κ = 1}; reason: by Lemma 5.10 this κ is unique
--   - encoding: R = √(L_D − λ₀X) = Σ_{i=1}^{d} √λ_i X^{2^{i−1}} → R defined as the coefficientwise square root of L_D − λ₀X; reason: the sum is the expansion of that root for the linearized locator
--   - encoding: union of cosets of a subspace of D of dimension d − 2t → invariance of the root set under an additive subgroup W ≤ D with 2^{d−2t} elements; reason: a W-invariant subset of D is a union of W-cosets
--   - encoding: in any field containing B → every field F' : Type with Algebra B F'; reason: every field containing B is an algebra over B
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), Lemma 5.12, p.41

import Mathlib
import Definitions.Def_GoldProxGap_quadPoly

open Polynomial

open scoped Classical

namespace GoldProxGap

/-- **Lemma 5.12 (Gold moments give polynomials with many roots)**, p.41. Dao, Kominers, Thaler,
Zheng, *Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*, STOC 2027
submission manuscript (2 November 2026, sha256 6c2d9ced…).

"Fix a basis ω₁, …, ω_d of the label space D̂, let 2 ≤ t ≤ d/2, and put T = N/2 − N/2^{t+1},
R = √(L_D − λ₀X) = Σ_{i=1}^{d} √λ_i X^{2^{i−1}}. Each alternating binary d × d matrix A of rank 2t
with M_1(A) = ⋯ = M_{t−1}(A) = 0 gives 2^{2t} distinct monic polynomials P = R + C ∈ B[X],
deg C = T/2 = N/4 − N/2^{t+2}, one for each label ω of Lemma 5.10. The roots of P on D are the T
points where ψ + κ takes the value one. The polynomials from different matrices are also
distinct. Every polynomial P of this family has the following properties.
1. It satisfies P′(P² + L_D) = λ₀P. (5.5)
2. Its set of roots on D is a union of cosets of a subspace of D of dimension d − 2t.
3. It takes the same value as any other polynomial of the family at at most N/2^{2t} points
outside D, in any field containing B."

**Formalization Note.**
* The basis of the label space is a coordinate basis `φs` of the linear functions,
  `ω_i = label D (φs i)`; a label `ω` is given by its linear function `φ`. The "labels ω of
  Lemma 5.10" for `A` are those making `ψ = psi φs A φ` vanish on the polar radical of `A`;
  `Adm A φ` collects the hypotheses on the pair `(A, ω)`.
* The family is a function `P` on pairs `(A, φ)`; "2^{2t} distinct polynomials for each A, and
  distinct across matrices" is injectivity of `P` on admissible pairs. "The T points where ψ + κ
  takes the value one", with `κ` the one of Lemma 5.10, is stated with an existential `κ` for
  which `ψ + κ` is one at exactly `T` points (by Lemma 5.10 that `κ` is unique).
* `R = Rpoly D = √(L_D − λ₀X)`; `deg C = T/2` is `natDegree (P − R) = T/2`.
* Property 2: some additive subgroup `W ≤ D` with `2^{d−2t}` elements such that the roots of `P`
  on `D` are invariant under translation by `W`.
* Property 3 quantifies over every field `F'` with `Algebra B F'` and counts the common points
  `β ∉ D` of two distinct members as roots of their difference. -/
theorem lemma_5_12 {B : Type} [Field B] [Fintype B] [CharP B 2] (D : AddSubgroup B) (d : ℕ)
    (hD : Nat.card D = 2 ^ d) (φs : Fin d → (D →+ ZMod 2)) (hφs : IsCoordBasis D φs)
    (t : ℕ) (ht : 2 ≤ t) (htd : 2 * t ≤ d) :
    let ω : Fin d → B := fun i => label D (φs i)
    let T := 2 ^ d / 2 - 2 ^ d / 2 ^ (t + 1)
    let R := Rpoly D
    let LD := locator (domainFinset D)
    let Adm : Matrix (Fin d) (Fin d) (ZMod 2) → (D →+ ZMod 2) → Prop := fun A φ =>
      IsAltBin A ∧ A.rank = 2 * t ∧ (∀ k, 1 ≤ k → k ≤ t - 1 → goldMoment ω A k = 0) ∧
      ∀ v ∈ polarRadical (psi φs A 0), psi φs A φ v = 0
    ∃ P : Matrix (Fin d) (Fin d) (ZMod 2) → (D →+ ZMod 2) → B[X],
      (∀ A φ, Adm A φ →
        (P A φ).Monic ∧ (P A φ - R).natDegree = T / 2 ∧
        (∃ κ : ZMod 2, (Finset.univ.filter (fun x : D => psi φs A φ x + κ = 1)).card = T ∧
          ∀ x : D, (P A φ).eval (x : B) = 0 ↔ psi φs A φ x + κ = 1) ∧
        derivative (P A φ) * ((P A φ) ^ 2 + LD) = C (lam0 D) * P A φ ∧
        ∃ W : AddSubgroup B, W ≤ D ∧ Nat.card W = 2 ^ (d - 2 * t) ∧
          ∀ x ∈ D, (P A φ).eval x = 0 → ∀ w ∈ W, (P A φ).eval (x + w) = 0) ∧
      (∀ A φ A' φ', Adm A φ → Adm A' φ' → (A, φ) ≠ (A', φ') → P A φ ≠ P A' φ') ∧
      (∀ (F' : Type) [Field F'] [Algebra B F'], ∀ A φ A' φ', Adm A φ → Adm A' φ' →
        (A, φ) ≠ (A', φ') →
        ((((P A φ - P A' φ').map (algebraMap B F')).roots.toFinset).filter
          (fun β => β ∉ pushDomain F' (domainFinset D))).card ≤ 2 ^ d / 2 ^ (2 * t)) := by sorry

end GoldProxGap
