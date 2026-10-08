-- Prove2me | Theorems.Thm_MatrixTail_Azuma_lemma7_7
-- name    : MatrixTail.Azuma.lemma7_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:25:51.529236+00:00
-- url     : https://prove2.me/theorems/e2184047-4ca9-4cb0-9def-5f124265bb8f
-- title:
--   Lemma 7.7 (Azuma cgf) — log E[e^{2εθX} | X] ≼ 2θ²A² when X² ≼ A²
-- statement:
--   Let $A$ be a fixed self-adjoint $d\times d$ complex matrix, let $\varepsilon$ be a Rademacher random variable and let $\theta\in\mathbb R$. For every self-adjoint matrix $x$ with $x^2\preceq A^2$,
--   $$
--   \log \mathbb E\, e^{2\varepsilon\theta x} \preceq 2\theta^2A^2 .
--   $$
--
--   In the paper the lemma is stated for a random self-adjoint matrix $X$ with $X^2\preceq A^2$ and a Rademacher $\varepsilon$ independent of $X$: $\log\mathbb E[e^{2\varepsilon\theta X}\mid X]\preceq 2\theta^2A^2$. Because $\varepsilon$ is independent of $X$, the conditional expectation given $X$ is the function $x\mapsto\mathbb E e^{2\varepsilon\theta x}$ evaluated at $X$, so the statement above, for every admissible value $x$, is the paper's lemma. It is the conditional bound on the matrix cumulant generating function of a symmetrized difference used at each step of the proof of the matrix Azuma inequality.
--
--   **Formalization Note** Exponential and logarithm are defined by the continuous functional calculus; $\mathbb E e^{2\varepsilon\theta x}$ is positive definite, so its logarithm is the paper's. The expectation is entrywise and $\preceq$ is the semidefinite order.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 29, Lemma 7.7 (Azuma cgf)

import Mathlib
import Definitions.Def_MatrixTail_Azuma_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Azuma

/-- **Lemma 7.7 (Azuma cgf).** Tropp, *User-Friendly Tail Bounds for Sums of Random Matrices*,
arXiv:1004.4389v7, p. 29: "Suppose that `X` is a random s.a. matrix and `A` is a fixed s.a. matrix that satisfy
`X² ≼ A²`. Let `ε` be a Rademacher random variable independent from `X`. Then
`log E[e^{2εθX} | X] ≼ 2θ²A²` for `θ ∈ ℝ`."

**Formalization Note.**
* Complex Hermitian `d × d` matrices; `exp`, `log` are `cfc Real.exp`, `cfc Real.log` (`mexp`, `mlog`); `E` is
  the entrywise expectation (`mean`); `≼` is the Loewner order under `MatrixOrder`.
* **The conditioning is resolved by independence.** Since `ε` is independent of `X`, the conditional
  expectation `E[e^{2εθX} | X]` is the function `x ↦ E e^{2εθx}` evaluated at `X`. The statement is therefore
  posed for every fixed Hermitian `x` with `x² ≼ A²` (the values `X` takes almost surely): for each such `x`,
  `log E e^{2εθx} ≼ 2θ²A²`. Applied at `x = X(ω)` this is the paper's almost-sure inequality. The content
  (`E e^{2εθx} = cosh(2θx) ≼ e^{2θ²x²}` and the operator monotonicity of `log` together with `x² ≼ A²`) is
  intact. `E e^{2εθx}` is positive definite, where `log` is the paper's (2.7).
* No integrability hypothesis: `ε = ±1` almost surely, so `e^{2εθx}` is bounded. `P` is a probability
  measure. -/
theorem lemma7_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (x A : Matrix (Fin d) (Fin d) ℂ) (hx : x.IsHermitian) (hA : A.IsHermitian)
    (hxA : x ^ 2 ≤ A ^ 2) (ε : Ω → ℝ) (hε : IsRademacher P ε) (θ : ℝ) :
    mlog (mean P (fun ω => mexp ((2 * ε ω * θ) • x))) ≤ (2 * θ ^ 2) • A ^ 2 := by sorry

end MatrixTail.Azuma
