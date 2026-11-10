-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_lemma_3_4_fourier_to_laplace
-- name    : GinibrePermanent977.Anticoncentration.lemma_3_4_fourier_to_laplace
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:10:12.877788+00:00
-- url     : https://prove2.me/theorems/4273d627-5676-4194-9dbc-c8aef8436b04
-- title:
--   Lemma 3.4 — Fourier-to-Laplace comparison
-- statement:
--   Let $X,Y$ be random column vectors in $\mathbb R^d$ (arbitrary laws). Suppose
--
--   $$
--   \operatorname{Re}E\,e^{it^*X}\le\operatorname{Re}E\,e^{it^*Y}\qquad(t\in\mathbb R^d).
--   $$
--
--   Then $YY^*\preceq_{Lt}XX^*$, that is, for every real symmetric positive semidefinite $T\in\mathbb R^{d\times d}$,
--
--   $$
--   E\,e^{-Y^*TY}\ge E\,e^{-X^*TX}.
--   $$
--
--   The lemma turns domination of characteristic functions into matrix Laplace-transform domination of outer products; it is applied on the underlying real space $\mathbb R^{\beta m}$ of $\mathbb K^m$.
--
--   Differences from the source:
--
--   - encoding: random vectors $X,Y$ → their laws $\mu,\nu$ (probability measures on $\mathbb R^d$); reason: both hypothesis and conclusion depend only on the laws
--   - encoding: $M\preceq_{Lt}N$ for $M=XX^*$, $N=YY^*$, tests $\operatorname{Re}\operatorname{tr}(TM)$, $T\succeq0$ Hermitian → `OuterLaplaceOrder` with $\operatorname{Re}(v^*Tv)$ written as $\sum_i(v_i,(Tv)_i)_{\mathbb R}$, $T$ Hermitian with nonnegative real quadratic form; reason: $\operatorname{Re}\operatorname{tr}(Tvv^*)=\operatorname{Re}(v^*Tv)$ by cyclicity of the real trace; every matrix compared in the paper is a rank-one outer product
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), §3.1, p. 8, Lemma 3.4 (Definition 1.4, p. 3) (PDF SHA-256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder Nat ENNReal

namespace GinibrePermanent977.Anticoncentration

/-- Lemma 3.4 (Fourier-to-Laplace comparison), p. 8. Let `X, Y` be random column vectors in `ℝ^d`
with laws `μ`, `ν`. If `Re E e^{i t^* X} ≤ Re E e^{i t^* Y}` for every `t ∈ ℝ^d`, then
`Y Y^* ⪯_{Lt} X X^*`, i.e. `E e^{-Y^* T Y} ≥ E e^{-X^* T X}` for every real symmetric `T ⪰ 0`. -/
theorem lemma_3_4_fourier_to_laplace {d : ℕ} (μ ν : Measure (Fin d → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ t : Fin d → ℝ,
      (∫ x, Complex.exp (Complex.I * ((t ⬝ᵥ x : ℝ) : ℂ)) ∂μ).re ≤
        (∫ y, Complex.exp (Complex.I * ((t ⬝ᵥ y : ℝ) : ℂ)) ∂ν).re) :
    OuterLaplaceOrder ν μ (fun y => y) (fun x => x) := by sorry

end GinibrePermanent977.Anticoncentration
