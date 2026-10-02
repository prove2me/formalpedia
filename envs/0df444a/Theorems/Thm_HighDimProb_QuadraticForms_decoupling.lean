-- Prove2me | Theorems.Thm_HighDimProb_QuadraticForms_decoupling
-- name    : HighDimProb.QuadraticForms.decoupling
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:28:41.607354+00:00
-- url     : https://prove2.me/theorems/91915416-6ee2-4c59-84bc-d581e1b1d28e
-- title:
--   Theorem 6.1.1 — Decoupling
-- statement:
--   This is the **Decoupling theorem**, the main proof engine of Chapter 6 of Vershynin's
--   *High-Dimensional Probability*: it replaces a quadratic form in dependent terms by a
--   bilinear form in two independent copies, at the cost of a universal constant factor $4$.
--
--   Let $A = (A_{ij})_{i,j=1}^n$ be an $n \times n$, **diagonal-free** matrix (every $A_{ii}
--   = 0$). Let $X = (X_1, \dots, X_n)$ be a random vector with independent, mean zero
--   coordinates $X_i$, and let $X' = (X_1', \dots, X_n')$ be an **independent copy** of $X$
--   (a random vector, independent of $X$, with the same coordinatewise distributions). Then,
--   for every convex function $F : \mathbb R \to \mathbb R$,
--
--   $$
--   \mathbb E\, F(X^\top A X) \;\le\; \mathbb E\, F(4 X^\top A X'),
--   \qquad X^\top A X = \sum_{i,j} A_{ij} X_i X_j,\ \ X^\top A X' = \sum_{i,j} A_{ij} X_i X_j'.
--   $$
--
--   The quadratic form $X^\top A X$ (a "chaos") has dependent terms, since $X_i X_j$ and
--   $X_i X_k$ share the factor $X_i$; the bilinear form $X^\top A X'$ is easier to analyze,
--   since conditioning on $X'$ turns it into a sum of independent random variables with fixed
--   coefficients. Decoupling is what lets the Hanson-Wright inequality (Theorem 6.2.1) reduce
--   the off-diagonal part of a quadratic form's tail to a bound on this bilinear form.
--
--   **Formalization Note** $X$ and $X'$ are two families of real random variables on one
--   probability space, jointly independent as a single family of $2n$ coordinates
--   (`iIndepFun` on `Fin n ⊕ Fin n`), which is stronger than the book's bare "$X'$ is
--   independent of $X$" but faithful to it here: it is exactly what "$X'$ is an independent
--   copy of $X$" gives once $X$ itself has independent coordinates. Each $X_i'$ having the
--   same distribution as $X_i$ is `IdentDistrib`. As in the convex decoupling lemma, both
--   quadratic/bilinear forms are required `Integrable` after applying $F$, and each $X_i$,
--   $X_i'$ is required `Integrable`, so that the mean-zero hypothesis and both sides of the
--   conclusion are genuine (not Mathlib's junk-value) expectations. The diagonal-free
--   hypothesis on $A$ is essential and is not the same statement as the goal theorem
--   (Hanson-Wright), where $A$ is a general matrix; see Remark 6.1.3 in the source for how
--   the general case is reduced to this one.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Theorem 6.1.1, p. 136 (PDF p. 144)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace HighDimProb.QuadraticForms

/-- **Theorem 6.1.1** (Decoupling), Vershynin, *High-Dimensional Probability* (2018), p. 136.

Let `A` be an `n × n`, diagonal-free matrix (i.e. the diagonal entries of `A` equal zero). Let
`X = (X₁, …, Xₙ)` be a random vector with independent mean zero coordinates `Xᵢ`. Then, for
every convex function `F : ℝ → ℝ`, one has `E F(XᵀAX) ≤ E F(4XᵀAX′)`, where `X′` is an
independent copy of `X`. -/
theorem decoupling {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X X' : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i)) (hX'_meas : ∀ i, Measurable (X' i))
    (hindep : iIndepFun (Sum.elim X X') P)
    (hX_int : ∀ i, Integrable (X i) P) (hX'_int : ∀ i, Integrable (X' i) P)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hX'_dist : ∀ i, IdentDistrib (X' i) (X i) P P)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, A i i = 0)
    (F : ℝ → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (hF1 : Integrable (fun ω => F (∑ i, ∑ j, A i j * X i ω * X j ω)) P)
    (hF2 : Integrable (fun ω => F (4 * ∑ i, ∑ j, A i j * X i ω * X' j ω)) P) :
    ∫ ω, F (∑ i, ∑ j, A i j * X i ω * X j ω) ∂P ≤
      ∫ ω, F (4 * ∑ i, ∑ j, A i j * X i ω * X' j ω) ∂P := by sorry

end HighDimProb.QuadraticForms
