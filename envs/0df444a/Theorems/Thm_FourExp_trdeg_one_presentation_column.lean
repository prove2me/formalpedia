-- Prove2me | Theorems.Thm_FourExp_trdeg_one_presentation_column
-- name    : FourExp.trdeg_one_presentation_column
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T07:40:34.235757+00:00
-- url     : https://prove2.me/theorems/97fdb3d7-a247-4be9-a6ac-2b2b9b44b0cb
-- title:
--   A transcendence-degree-one field as quotients of integer polynomials in ω and ω₁, when only e^{x₁y₂} and e^{x₂y₂} are algebraic
-- statement:
--   Let $x_1, x_2$ be $\mathbb{Q}$-linearly independent, and likewise $y_1, y_2$. Suppose that $e^{x_1y_2}$ and $e^{x_2y_2}$ are algebraic and that
--
--   $$\operatorname{trdeg}_{\mathbb{Q}}\, \mathbb{Q}[x_1, x_2, y_1, y_2, e^{x_1y_1}, e^{x_2y_1}] \le 1.$$
--
--   Then there are $\omega, \omega_1 \in \mathbb{C}$ with $\omega$ transcendental; $Q \in \mathbb{Z}[X][Y]$, monic in $Y$ of positive degree $d$, with $Q(\omega, \omega_1) = 0$ and minimal there: no non-zero $A \in \mathbb{Z}[X][Y]$ of $Y$-degree less than $d$ vanishes at $(\omega, \omega_1)$; and $D, E_i, G_j, H_{ij} \in \mathbb{Z}[X][Y]$ with $D(\omega, \omega_1) \neq 0$ and $x_iD = E_i$, $y_jD = G_j$, $e^{x_iy_j}D = H_{ij}$ at $(\omega, \omega_1)$.
--
--   This is the reduction to $\omega$ on p. 196 of Waldschmidt (1973), and `FourExp.trdeg_one_presentation` with only $e^{x_1y_2}$, $e^{x_2y_2}$ assumed algebraic and with $e^{x_1y_1}$, $e^{x_2y_1}$ joining $x_1, x_2, y_1, y_2$ in the transcendence-degree hypothesis; the conclusion is the same. Here $\omega = x_1y_2$, which is transcendental by Hermite–Lindemann, and `Transcendence.exists_monic_integral_model_presentation` presents all eight numbers at once. The hypotheses never hold together, by `DiazModulus.two_algebraically_independent_of_exp_column`: this node is a step of its proof by contradiction.
-- source:
--   The reduction to ω at the start of the proof of the Théorème in M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, p. 196. Formal proof: Diaz modulus mission, 30 September 2026 (C. Perassi).

import Mathlib

namespace FourExp

/-- The column data in transcendence degree one, presented over one integral model.

Let `x₁, x₂` and `y₁, y₂` be `ℚ`-linearly independent, with `e^{x₁y₂}` and `e^{x₂y₂}` algebraic,
and suppose that `ℚ[x₁, x₂, y₁, y₂, e^{x₁y₁}, e^{x₂y₁}]` has transcendence degree at most one.
Write `φ(P) = P(ω, ω₁)` for `P ∈ ℤ[X][Y]`. Then there are a transcendental `ω`, a number `ω₁`, a
polynomial `Q ∈ ℤ[X][Y]` monic in `Y` of positive degree with `φ(Q) = 0` and no non-zero
`A ∈ ℤ[X][Y]` of smaller `Y`-degree with `φ(A) = 0`, and polynomials `D, Eᵢ, Gⱼ, Hᵢⱼ` with
`δ = φ(D) ≠ 0`, `xᵢ δ = φ(Eᵢ)`, `yⱼ δ = φ(Gⱼ)` and `e^{xᵢyⱼ} δ = φ(Hᵢⱼ)`.

This is `FourExp.trdeg_one_presentation` with the column hypothesis in place of the four algebraic
exponentials; the conclusion is unchanged. Here `ω = x₁ y₂` works: it is non-zero and `e^ω` is
algebraic, so it is transcendental by Hermite–Lindemann. The exponentials `e^{x₁y₁}`, `e^{x₂y₁}`
are algebraic over `ℚ(ω)` only, so `H₀₀` and `H₁₀` really depend on `X`. -/
theorem trdeg_one_presentation_column
    (x₁ x₂ y₁ y₂ : ℂ) (hx : LinearIndependent ℚ ![x₁, x₂]) (hy : LinearIndependent ℚ ![y₁, y₂])
    (hexp₂ : ∀ i : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * y₂)))
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁),
      Complex.exp (x₂ * y₁)} : Set ℂ)) ≤ 1) :
    ∃ ω ω₁ : ℂ, Transcendental ℚ ω ∧ ∃ Q : Polynomial (Polynomial ℤ),
        Q.Monic ∧ 0 < Q.natDegree ∧ Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0 ∧
        (∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree → Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0) ∧
        ∃ (D : Polynomial (Polynomial ℤ)) (E G : Fin 2 → Polynomial (Polynomial ℤ)) (H : Fin 2 → Fin 2 → Polynomial (Polynomial ℤ)),
          Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ≠ 0 ∧ (∀ i, ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i)) ∧
          (∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j)) ∧
          (∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (H i j)) := by
  sorry

end FourExp
