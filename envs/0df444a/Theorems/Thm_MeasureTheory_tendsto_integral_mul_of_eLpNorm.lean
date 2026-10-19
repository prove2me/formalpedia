-- Prove2me | Theorems.Thm_MeasureTheory_tendsto_integral_mul_of_eLpNorm
-- name    : MeasureTheory.tendsto_integral_mul_of_eLpNorm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T22:09:43.214409+00:00
-- url     : https://prove2.me/theorems/44eaf7b8-eace-4669-89e8-627d987b4a1b
-- title:
--   Compact continuous pairings respect Lp convergence
-- statement:
--   Let $\mu$ be a locally finite Borel measure on $\mathbb R^n$, $1\le p<\infty$, and $u_j,v\in L^p(\mu)$. If $\|u_j-v\|_p\to0$, then for every continuous compactly supported $\psi$,
--   $$\int u_j\psi\,d\mu\longrightarrow\int v\psi\,d\mu.$$
--   The compact support has finite measure and the conjugate exponent estimate controls the integral difference; at $p=1$ use the supremum norm of $\psi$. The formulation covers restricted volume and boundary volume, including dimension zero.
-- source:
--   Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Mathlib/MeasureTheory/Integral/Bochner/Basic.lean, tendsto_integral_of_L1, and the Holder inequality for conjugate Lp exponents in Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean. Standard compact-test consequence used in Hunter, Notes on PDEs, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Theorems 3.42–3.44, printed pp. 72–73.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
open MeasureTheory Filter
open scoped ENNReal Topology
set_option autoImplicit false

theorem MeasureTheory.tendsto_integral_mul_of_eLpNorm {n : ℕ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsLocallyFiniteMeasure μ]
    (u : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ∀ j, MemLp (u j) p μ) (hv : MemLp v p μ)
    (hlim : Tendsto (fun j => eLpNorm (u j - v) p μ) atTop (𝓝 0))
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Tendsto (fun j => ∫ x, u j x * ψ x ∂μ) atTop (𝓝 (∫ x, v x * ψ x ∂μ)) := by sorry
