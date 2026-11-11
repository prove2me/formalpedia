-- Prove2me | Theorems.Thm_GoldProxGap_lemma_5_6
-- name    : GoldProxGap.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:25:25.936433+00:00
-- url     : https://prove2.me/theorems/ab91f17e-a5c3-4dfc-811a-000dadd1daf9
-- title:
--   Lemma 5.6 — the polynomial $Q$ of a quadratic function: $\deg Q<N$, $Q|_D=\psi$, $Q'=J+\varepsilon_A+\omega^2$, $Q^2+Q=\Lambda Q'$
-- statement:
--   **Lemma 5.6 (The polynomial of a quadratic function).** In the setting of (5.2) (a basis $\omega_1,\dots,\omega_d$ of the label space, an alternating binary matrix $A$, a label $\omega$):
--   1. The polynomial $Q$ has degree less than $N$, satisfies $Q(0)=0$, and agrees with $\psi$ on $D$.
--   2. Its derivative is $Q'=J+\varepsilon_A+\omega^2$, and
--   $$
--   Q^2+Q=\Lambda Q'.
--   $$
--   3. The polar radical of $\psi$ is $\{y\in D: J(y)=0\}$.
--
--   The identity $Q^2+Q=\Lambda Q'$ is what lets a quadratic Boolean function be turned into a polynomial with many roots once its derivative is a square of low degree.
--
--   **Formalization Note** The values of $\psi$ in $\mathbb F_2$ are compared with $Q(x)\in\mathbb B$ as $0,1\in\mathbb B$.
--
--   Differences from the source:
--   - encoding: a basis ω₁, …, ω_d of the label space D̂ → a coordinate basis φs of the linear functions D → F₂ with ω_i = label(φs i); reason: by Lemma 5.5(2) the label map is an F₂-linear bijection, so this is the same data
--   - encoding: a label ω of ψ → the linear function φ of the label, with ω = label(φ); reason: every label is the label of a linear function
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), Lemma 5.6, pp.38–39

import Mathlib
import Definitions.Def_GoldProxGap_quadPoly

open Polynomial

open scoped Classical

namespace GoldProxGap

/-- **Lemma 5.6 (The polynomial of a quadratic function)**, pp.38–39. Dao, Kominers, Thaler,
Zheng, *Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*, STOC 2027
submission manuscript (2 November 2026, sha256 6c2d9ced…).

"Let ψ, Q, J, and ε_A be as above.
1. The polynomial Q has degree less than N, satisfies Q(0) = 0, and agrees with ψ on D.
2. Its derivative is Q′ = J + ε_A + ω², and Q² + Q = ΛQ′. (5.3)
3. The polar radical of ψ is {y ∈ D : J(y) = 0}."

"As above" is (5.2), p.38: a basis `ω₁, …, ω_d` of the label space, an alternating binary
`d × d` matrix `A`, a label `ω`.

**Formalization Note.** The basis of the label space is a coordinate basis `φs` of the linear
functions `D → F₂` (`ω_i = label D (φs i)`), the label `ω` of `ψ` is given by its linear function
`φ` (`ω = label D φ`); see `GoldProxGap.label`, `GoldProxGap.quadPoly`. `ψ = psi φs A φ`,
`Q = Qpoly D φs A φ`, `J = Jpoly D φs A`, `ε_A = epsA D φs A`, `Λ = normLocator D`. The value of
`ψ` in `F₂` is compared with `Q(x) ∈ B` through `0, 1 ∈ B`. -/
theorem lemma_5_6 {B : Type} [Field B] [Fintype B] [CharP B 2] (D : AddSubgroup B) (d : ℕ)
    (hD : Nat.card D = 2 ^ d) (φs : Fin d → (D →+ ZMod 2)) (hφs : IsCoordBasis D φs)
    (A : Matrix (Fin d) (Fin d) (ZMod 2)) (hA : IsAltBin A) (φ : D →+ ZMod 2) :
    let Q := Qpoly D φs A φ
    Q.degree < ((2 ^ d : ℕ) : WithBot ℕ) ∧ Q.eval 0 = 0 ∧
    (∀ x : D, Q.eval (x : B) = ((psi φs A φ x).val : B)) ∧
    derivative Q = Jpoly D φs A + C (epsA D φs A + label D φ ^ 2) ∧
    Q ^ 2 + Q = normLocator D * derivative Q ∧
    polarRadical (psi φs A φ) = Finset.univ.filter (fun y : D => (Jpoly D φs A).eval (y : B) = 0) := by sorry

end GoldProxGap
