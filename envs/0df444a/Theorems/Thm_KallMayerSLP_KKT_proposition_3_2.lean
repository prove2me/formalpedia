-- Prove2me | Theorems.Thm_KallMayerSLP_KKT_proposition_3_2
-- name    : KallMayerSLP.KKT.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:09:32.611882+00:00
-- url     : https://prove2.me/theorems/6f5c6430-5c2a-4929-8e36-b2a82075a88b
-- title:
--   Proposition 3.2 — the subdifferential of a convex function: nonempty convex compact, singleton iff differentiable, affine chain rule
-- statement:
--   Let $\varphi:\mathbb R^n\to\mathbb R$ be convex. Then:
--
--   1. for every $x\in\mathbb R^n$ the subdifferential $\partial\varphi(x)$ is nonempty, convex, closed and bounded;
--   2. $\varphi$ is differentiable at $x$ with gradient $\hat g=\nabla\varphi(x)$ if and only if $\partial\varphi(x)=\{\hat g\}$;
--   3. for every convex $\psi:\mathbb R^m\to\mathbb R$, every $d\in\mathbb R^m$ and every matrix $D\in\mathbb R^{m\times n}$, the composition $f(x):=\psi(d+Dx)$ is convex, and the chain rule
--   $$
--   \partial f(x)=D^{\mathsf T}\,\partial\psi(d+Dx),\qquad\text{i.e.}\qquad h\in\partial f(x)\iff\exists\,g\in\partial\psi(d+Dx):\ h=D^{\mathsf T}g,
--   $$
--   holds for every $x\in\mathbb R^n$.
--
--   These are the basic facts on subgradients that the book uses for nonsmooth convex functions, in particular for the recourse functions of later chapters.
--
--   **Formalization Note** "Differentiable at $x$ with gradient $\hat g$" is `HasGradientAt φ ĝ x`; $D$ acts as `Matrix.toEuclideanLin D` and $D^{\mathsf T}$ as `Matrix.toEuclideanLin Dᵀ`.
--
--   Differences from the source:
--   - encoding: ℝⁿ with zᵀv → EuclideanSpace ℝ (Fin n) with the inner product ⟪z, v⟫ and Mathlib's gradient; reason: Lean convention; the same space and the same gradient for differentiable functions
--   - encoding: φ differentiable in x with gradient ĝ → HasGradientAt φ ĝ x; reason: Fréchet differentiability with gradient ĝ, the book's notion on ℝⁿ
--   - encoding: matrix D ∈ ℝ^{m×n} and Dᵀ → Matrix.toEuclideanLin D and Matrix.toEuclideanLin Dᵀ; reason: the linear maps x ↦ Dx and g ↦ Dᵀg on Euclidean space
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3, Proposition 3.2, p.61 (PDF 72)

import Mathlib
import Definitions.Def_KallMayerSLP_KKT_subdifferential

open Matrix

namespace KallMayerSLP.KKT

/-- **Proposition 3.2 (subdifferential of a convex function).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, Proposition 3.2, p.61 (PDF 72):
"Given a convex function `φ : ℝⁿ → ℝ`, then for any `x ∈ ℝⁿ` the set `∂φ(x)` is nonempty,
convex, closed, and bounded. In addition, `φ` is differentiable in `x` with the gradient
`ĝ = ∇φ(x)` if and only if `∂φ(x) = {ĝ}`, i.e. `∂φ(x)` is a singleton. Finally, given a convex
function `ψ : ℝᵐ → ℝ` and a linear affine mapping `y : ℝⁿ → ℝᵐ` defined by `y(x) := d + Dx` with
some `d ∈ ℝᵐ` and `D ∈ ℝ^{m×n}`, then `f : ℝⁿ → ℝ` composed as `f(x) := ψ(y(x))` is convex, and
for its subdifferential holds the chain rule `∂f(x) = Dᵀ∂ψ(y(x))`, or equivalently
`h ∈ ∂f(x) ⟺ ∃g ∈ ∂ψ(y(x)) : h = Dᵀg`."

**Formalization Note.** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`; "convex" is `ConvexOn ℝ Set.univ`;
"differentiable in `x` with gradient `ĝ`" is `HasGradientAt φ ĝ x` (Fréchet differentiability with
gradient `ĝ`); the matrix `D` acts as `Matrix.toEuclideanLin D`, and `Dᵀ` as
`Matrix.toEuclideanLin Dᵀ`. The three sentences are the three conjuncts. -/
theorem proposition_3_2 {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ConvexOn ℝ Set.univ φ) :
    (∀ x, (subdifferential φ x).Nonempty ∧ Convex ℝ (subdifferential φ x) ∧
        IsClosed (subdifferential φ x) ∧ Bornology.IsBounded (subdifferential φ x)) ∧
    (∀ x ĝ, HasGradientAt φ ĝ x ↔ subdifferential φ x = {ĝ}) ∧
    (∀ (m : ℕ) (ψ : EuclideanSpace ℝ (Fin m) → ℝ), ConvexOn ℝ Set.univ ψ →
      ∀ (d : EuclideanSpace ℝ (Fin m)) (D : Matrix (Fin m) (Fin n) ℝ),
        ConvexOn ℝ Set.univ (fun x => ψ (d + Matrix.toEuclideanLin D x)) ∧
        ∀ x h, h ∈ subdifferential (fun x => ψ (d + Matrix.toEuclideanLin D x)) x ↔
          ∃ g ∈ subdifferential ψ (d + Matrix.toEuclideanLin D x),
            h = Matrix.toEuclideanLin Dᵀ g) := by sorry

end KallMayerSLP.KKT
