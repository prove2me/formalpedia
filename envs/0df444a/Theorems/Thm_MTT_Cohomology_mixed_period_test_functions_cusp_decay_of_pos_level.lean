-- Prove2me | Theorems.Thm_MTT_Cohomology_mixed_period_test_functions_cusp_decay_of_pos_level
-- name    : MTT.Cohomology.mixed_period_test_functions_cusp_decay_of_pos_level
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-08T08:05:20.576447+00:00
-- url     : https://prove2.me/theorems/d4862a5c-8592-4e25-87e7-040dcbca2986
-- title:
--   Cusp decay of mixed-period test functions at positive level
-- statement:
--   Let $N>0$ and $k\ge2$. Let $g,v,q\in S_k(\Gamma_1(N))$ and let $U$ be a mixed-period primitive for $(g,v)$, with the coefficient growth specified by `IsMixedPeriodPrimitive`. Put $n=k-2$ and define on the upper half-plane
--   $$A_1(z)=B_n\big(U(z),\overline{q(z)}(\bar zX+Y)^n\big),\qquad
--   A_2(z)=\overline{B_n\big(q(z)(zX+Y)^n,U(z)\big)}.$$
--   For every $\sigma=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\mathrm{SL}_2(\mathbb Z)$, both normalized cusp-chart functions vanish at infinity:
--   $$\frac{A_i(\sigma z)}{\overline{cz+d}^{\,2}}\longrightarrow0\quad\text{as }\operatorname{Im}z\to\infty,\qquad i=1,2.$$
--   The convergence is uniform in the real part, as expressed by Mathlib's `IsZeroAtImInfty`. This is the cusp-boundary input for the mixed-period Stokes argument. Positive level is explicit; the theorem makes no claim for $\Gamma_1(0)$.
--
--   **Formalization Note** Outside the upper half-plane, the scalar test functions use Mathlib's standard extension of functions on the upper half-plane. This declaration replaces `MTT.Cohomology.mixed_period_test_functions_cusp_decay`, whose statement omitted $0<N$.
-- source:
--   Classical mixed Eichler--Shimura period pairing argument: contraction invariance, Wirtinger differentiation, and exponential decay of cusp forms.

import Definitions.Def_MTT_PeriodPairing
import Mathlib.NumberTheory.ModularForms.Bounds

set_option autoImplicit false
noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
open MTT.Cohomology

theorem MTT.Cohomology.mixed_period_test_functions_cusp_decay_of_pos_level
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U) :
    let A₁ : ℂ → ℂ := fun z =>
      periodContraction (k - 2) (U z)
        (conj ((↑ₕ(fun τ : ℍ ↦ q τ)) z) • periodPower (k - 2) (conj z))
    let A₂ : ℂ → ℂ := fun z => conj <|
      periodContraction (k - 2)
        (((↑ₕ(fun τ : ℍ ↦ q τ)) z) • periodPower (k - 2) z) (U z)
    (∀ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ, IsZeroAtImInfty
      fun τ : ℍ ↦ A₁ ((σ • τ : ℍ) : ℂ) *
        ((starRingEnd ℂ (denom σ τ)) ^ 2)⁻¹) ∧
    (∀ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ, IsZeroAtImInfty
      fun τ : ℍ ↦ A₂ ((σ • τ : ℍ) : ℂ) *
        ((starRingEnd ℂ (denom σ τ)) ^ 2)⁻¹) := by sorry
