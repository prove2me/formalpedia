-- Prove2me | Theorems.Thm_JHolomorphic_exists_memLp_eq_integral_inner
-- name    : JHolomorphic.exists_memLp_eq_integral_inner
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T20:41:56.916181+00:00
-- url     : https://prove2.me/theorems/0224d380-5de7-426c-aa91-5ab986b72fcb
-- title:
--   Continuous linear functionals on $L^p(\mu;E)$ are given by $L^q$ functions
-- statement:
--   Let $\mu$ be a $\sigma$-finite measure, let $E$ be a finite-dimensional real inner product space, let $1<p<\infty$ and let $q$ be the conjugate exponent, $\frac1p+\frac1q=1$. Then every continuous linear functional $\ell$ on $L^p(\mu;E)$ is represented by an element of $L^q(\mu;E)$: there is $G\in L^q(\mu;E)$ with
--   $$\ell(h)=\int \langle h(x),G(x)\rangle\,d\mu(x)\qquad\text{for all } h\in L^p(\mu;E).$$
--   This identifies the dual of $L^p(\mu;E)$ with $L^q(\mu;E)$ and is used to turn functionals bounded in an $L^p$ norm into functions.
--
--   **Formalization Note** The functional is `ℓ : Lp E p μ →L[ℝ] ℝ` with `p q : ℝ≥0∞`, `[Fact (1 ≤ p)]`, `[p.HolderConjugate q]`, `1 < p` and `p ≠ ⊤`. The representing function is a plain function `G : α → E` with `MemLp G q μ`, and the pairing is `∫ x, inner ℝ (h x) (G x) ∂μ`, where `h x` is the chosen representative of the class `h`.
-- source:
--   Standard; cf. W. Rudin, Real and Complex Analysis, Theorem 6.16; G. B. Folland, Real Analysis, Theorem 6.15

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.ENNReal.Holder

namespace JHolomorphic

open MeasureTheory
open scoped ENNReal

/-- Let `μ` be σ-finite, `E` a finite-dimensional real inner product space, `1 < p < ∞` and `q`
the conjugate exponent. Every continuous linear functional `ℓ` on `L^p(μ; E)` is of the form
`ℓ h = ∫ ⟪h, G⟫ dμ` for some `G ∈ L^q(μ; E)`. -/
theorem exists_memLp_eq_integral_inner {α E : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [p.HolderConjugate q] (hp : 1 < p) (hp' : p ≠ ⊤)
    (ℓ : Lp E p μ →L[ℝ] ℝ) :
    ∃ G : α → E, MemLp G q μ ∧ ∀ h : Lp E p μ, ℓ h = ∫ x, inner ℝ (h x) (G x) ∂μ := by
  sorry

end JHolomorphic
