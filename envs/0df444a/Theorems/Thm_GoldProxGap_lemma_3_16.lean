-- Prove2me | Theorems.Thm_GoldProxGap_lemma_3_16
-- name    : GoldProxGap.lemma_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:23:12.646217+00:00
-- url     : https://prove2.me/theorems/f8664aec-a734-441f-a82d-68378b2de7b2
-- title:
--   Lemma 3.16 — from Boolean polynomials to witnesses: $P=\sqrt{H'/\lambda}\,L_D/H$ has exactly $T$ roots, and $a=P(\beta)+\sqrt{L_D(\beta)}$ is a nonzero exceptional challenge
-- statement:
--   **Lemma 3.16 (From Boolean polynomials to witnesses).** Let $D$ be binary additive of size $N\ge8$ in a finite field $\mathbb B$, put $K=N/4$ and $\lambda=L_D'$, and fix $\beta\in\mathbb F\setminus D$ in a finite extension $\mathbb F$. Suppose $H\in\mathbb B[X]$ has degree $N-T$, all its roots are distinct and lie in $D$, and
--   $$
--   H^2+H=(L_D/\lambda)H',\qquad 2\le T<N/2,\qquad T\ \text{even}.
--   $$
--   Then $P=\sqrt{H'/\lambda}\cdot L_D/H$ and $R=\sqrt{L_D-\lambda X}$ are polynomials, $P^2=L_D+L_D/H$, $P$ has exactly $T$ roots on $D$, and $\deg(P+R)=T/2$. For the fixed pair
--   $$
--   f(x)=\frac{R(x)+\sqrt{\lambda\beta}}{x-\beta},\qquad g(x)=\frac1{x-\beta},
--   $$
--   the challenge $a=P(\beta)+\sqrt{L_D(\beta)}$ is nonzero and has a witness of degree at most $T/2-1$ with exactly $T$ agreements. Moreover $a^2=L_D(\beta)/H(\beta)$, $\mathrm{agr}_K(f)\le 3N/8-1$ and $\mathrm{agr}_K(g)=\mathrm{CA}_K(f,g)=K$. In particular, distinct values $H(\beta)$ give distinct nonzero challenges for this same pair.
--
--   This conversion turns each polynomial $H$ of a Boolean function into one exceptional challenge of one fixed received pair.
--
--   **Formalization Note** Square roots are inverse Frobenius, and $\sqrt{H'/\lambda}$ is the coefficientwise square root of $\lambda^{-1}H'$; "are polynomials" is stated as: $R^2=L_D-\lambda X$, this root squares to $\lambda^{-1}H'$, and $H$ divides $L_D$. Polynomials over $\mathbb B$ are evaluated in $\mathbb F$ along the algebra map, and the code over $\mathbb F$ lives on the image of $D$.
--
--   Differences from the source:
--   - reading: all its roots are distinct and lie in D → H has deg H roots in B counted with multiplicity, they are pairwise distinct, and each lies in D; reason: the roots of H are those in a splitting field; the proof uses H | L_D, which needs all of them
--   - encoding: P = √(H′/λ) · L_D/H, R = √(L_D − λX) are polynomials → R (the coefficientwise square root of L_D − λX) squares to L_D − λX, the coefficientwise square root of λ⁻¹H′ squares to λ⁻¹H′, H divides L_D, and P is their product with L_D/H; reason: same claim
--   - encoding: fix β ∈ F \ D in a finite extension → a finite field F with Algebra B F and the instance [CharP F 2], β outside the image of D; reason: the characteristic of F follows from Algebra B F
--   - encoding: distinct values H(β) give distinct nonzero challenges → for two polynomials H, H' satisfying the hypotheses (with their own T, T'), H(β) ≠ H'(β) implies a(H) ≠ a(H'); reason: same claim
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), Lemma 3.16, p.24

import Mathlib
import Definitions.Def_GoldProxGap_reedSolomon
import Definitions.Def_GoldProxGap_domainFinset
import Definitions.Def_GoldProxGap_locator

open Polynomial

open scoped Classical

namespace GoldProxGap

/-- **Lemma 3.16 (From Boolean polynomials to witnesses)**, p.24. Dao, Kominers, Thaler, Zheng,
*Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*, STOC 2027 submission
manuscript (2 November 2026, sha256 6c2d9ced…).

"Let D be binary additive of size N ≥ 8 in a finite field B, put K = N/4 and λ = L′_D, and fix
β ∈ F \ D in a finite extension. Suppose H ∈ B[X] has degree N − T, all its roots are distinct and
lie in D, and H² + H = (L_D/λ)H′, 2 ≤ T < N/2, T even. Then P = √(H′/λ) · L_D/H,
P² = L_D + L_D/H, R = √(L_D − λX) are polynomials, P has exactly T roots on D, and
deg(P + R) = T/2. For the fixed pair f(x) = (R(x) + √(λβ))/(x − β), g(x) = 1/(x − β), the challenge
a = P(β) + √(L_D(β)) is nonzero and has a witness of degree at most T/2 − 1 with exactly T
agreements. Moreover, a² = L_D(β)/H(β), agr_K(f) ≤ 3N/8 − 1, agr_K(g) = CA_K(f, g) = K. In
particular, distinct values H(β) give distinct nonzero challenges for this same pair."

**Formalization Note.**
* `B` is a finite field of characteristic two and `D : AddSubgroup B` with `|D| = N ≥ 8`; `F` is
  a finite field with `Algebra B F`, and the code over `F` lives on the image of `D` in `F`
  (`pushDomain`). Polynomials over `B` are evaluated in `F` through `Polynomial.map`.
* `λ = locLam D` (the constant `L′_D`); square roots are `frobRoot · 2 1`; `R = polyRoot 2 1 (L_D − λX)`
  and `√(H′/λ) = polyRoot 2 1 (λ⁻¹ H′)`. "Are polynomials" is stated as: `R² = L_D − λX`
  (independent of `H`), the root of `λ⁻¹ H′` squares to `λ⁻¹ H′`, and `H ∣ L_D`; then
  `P = √(H′/λ) · (L_D / H)`.
* "All its roots are distinct and lie in D" is read as: `H` has `deg H` roots in `B` counted with
  multiplicity, they are pairwise distinct, and each lies in `D`.
* The pair `(f, g)` does not depend on `H`; the challenge `a = chal H` does. The last clause
  compares the challenges of two polynomials `H`, `H'` satisfying the hypotheses (with their own
  `T`, `T'`).
* `[CharP F 2]` is stated for `F`; it follows from `Algebra B F` and is needed for `frobRoot F 2 1`. -/
theorem lemma_3_16 {B : Type} [Field B] [Fintype B] [CharP B 2] (D : AddSubgroup B)
    (hN : 8 ≤ Nat.card D) {F : Type} [Field F] [Fintype F] [Algebra B F] [CharP F 2] (β : F)
    (hβ : β ∉ pushDomain F (domainFinset D)) :
    let N := Nat.card D
    let K := N / 4
    let LD := locator (domainFinset D)
    let lam := locLam (domainFinset D)
    let R := polyRoot 2 1 (LD - C lam * X)
    let DF := pushDomain F (domainFinset D)
    let f : DF → F := fun x =>
      ((R.map (algebraMap B F)).eval (x : F) + frobRoot F 2 1 (algebraMap B F lam * β)) /
        ((x : F) - β)
    let g : DF → F := fun x => 1 / ((x : F) - β)
    let P : B[X] → B[X] := fun H => polyRoot 2 1 (C lam⁻¹ * derivative H) * (LD / H)
    let chal : B[X] → F := fun H =>
      ((P H).map (algebraMap B F)).eval β + frobRoot F 2 1 ((LD.map (algebraMap B F)).eval β)
    let Hyp : B[X] → ℕ → Prop := fun H T =>
      H.natDegree = N - T ∧ Multiset.card H.roots = H.natDegree ∧ H.roots.Nodup ∧
      (∀ r ∈ H.roots, r ∈ D) ∧ H ^ 2 + H = C lam⁻¹ * LD * derivative H ∧
      2 ≤ T ∧ T < N / 2 ∧ Even T
    R ^ 2 = LD - C lam * X ∧
    agr DF K g = K ∧ CA DF K f g = K ∧ agr DF K f ≤ 3 * N / 8 - 1 ∧
    ∀ (H : B[X]) (T : ℕ), Hyp H T →
      (polyRoot 2 1 (C lam⁻¹ * derivative H)) ^ 2 = C lam⁻¹ * derivative H ∧
      H ∣ LD ∧
      (P H) ^ 2 = LD + LD / H ∧
      ((domainFinset D).filter (fun x => (P H).eval x = 0)).card = T ∧
      (P H + R).natDegree = T / 2 ∧
      chal H ≠ 0 ∧
      (∃ h : F[X], h.degree ≤ ((T / 2 - 1 : ℕ) : WithBot ℕ) ∧ polyAgree (f + chal H • g) h = T) ∧
      chal H ^ 2 = (LD.map (algebraMap B F)).eval β / (H.map (algebraMap B F)).eval β ∧
      ∀ (H' : B[X]) (T' : ℕ), Hyp H' T' →
        (H.map (algebraMap B F)).eval β ≠ (H'.map (algebraMap B F)).eval β →
        chal H ≠ chal H' := by sorry

end GoldProxGap
