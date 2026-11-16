-- Prove2me | Theorems.Thm_GuanQinQDP_Restricted_Supplement_measure_prepare_sandwich
-- name    : GuanQinQDP.Restricted.Supplement.measure_prepare_sandwich
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:36:31.81816+00:00
-- url     : https://prove2.me/theorems/aae6c99b-a6db-41ca-a05a-336afbd997a4
-- title:
--   Lemma 5.3 — measure-and-prepare sandwich $\Lambda\preceq_{\mathrm{CP}}T\preceq_{\mathrm{CP}}g(r)\Lambda$, with optimality of $g(r)$
-- statement:
--   Let $\Lambda:M_2\to M_2$ be a completely positive and unital map ($\Lambda(I)=I$; $\Lambda$ need not preserve the trace). Let $1\le r<\infty$ satisfy
--   $$\lambda_{\max}(\Lambda(N))\le r\,\lambda_{\min}(\Lambda(N))\qquad\text{for every }N\succeq0,$$
--   where $\lambda_{\max},\lambda_{\min}$ are the largest and smallest eigenvalues. The bound $r$ need not be the smallest one. Write $g(r)=\max\{1,(2r-1)/3\}$.
--
--   1. There is a measure-and-prepare map $T(N)=\sum_x\operatorname{Tr}(\tau_xN)F_x$, with finitely many states $\tau_x$ and operators $F_x\succeq0$, such that
--   $$\Lambda\preceq_{\mathrm{CP}}T\preceq_{\mathrm{CP}}g(r)\Lambda,$$
--   that is, $T-\Lambda$ and $g(r)\Lambda-T$ are completely positive.
--   2. No smaller coefficient depending only on $r$ suffices. For every $r\ge1$ and every $t<g(r)$ there is a completely positive unital $\Lambda$ satisfying the spectral bound with this $r$ for which no measure-and-prepare $T$ satisfies $\Lambda\preceq_{\mathrm{CP}}T\preceq_{\mathrm{CP}}t\Lambda$.
--
--   Applied to the adjoint $A_j^\dagger$ of a qubit channel with pure-privacy factor $r_j$, the lemma replaces $A_j^\dagger$ by a measure-and-prepare map at multiplicative cost $g(r_j)$, simultaneously for an event and its complement. This is the first step of the unrestricted composition bound (Theorem 5.5).
--
--   Differences from the source:
--
--   - encoding: λmax(Λ(N)) ≤ r λmin(Λ(N)) for all N ⪰ 0 → SpectralRatioLe Λ r: for every N ⪰ 0 and every proof h that Λ(N) is Hermitian, ⨆ eigenvalues ≤ r · ⨅ eigenvalues; reason: Λ(N) is Hermitian for completely positive Λ and N ⪰ 0, so the condition is the same
--   - encoding: 1 ≤ r < ∞ → r : ℝ with 1 ≤ r; reason: a real number is finite
--   - encoding: T(N) = ∑_x Tr(τ_x N) F_x over an index set x → IsMeasurePrepare T: a finite index set Fin m; reason: the source sums over a finite set (a separable decomposition of a two-qubit operator)
--   - reading: No smaller coefficient depending only on r suffices → for every r ≥ 1 and every real t < g(r) there is a CP unital Λ satisfying the hypothesis with this r and no measure-and-prepare T with Λ ⪯_CP T ⪯_CP tΛ; reason: the pointwise reading (failure at every r), which is what Remark 5.4 shows and which implies that every coefficient c(r) with c(r) < g(r) for some r fails
-- source:
--   Ji Guan, Yecheng Qin, Parallel Composition of Quantum Differential Privacy: The Role of Measurement Restrictions, STOC 2027 submission #1640 (October 2026), source.pdf SHA-256 da23c8347251683a16df4c61de3fa1604211cdbf34d757a7a45feb0efd54c694, Lemma 5.3 (printed p. 22 / PDF p. 23), proof printed pp. 22–24 / PDF pp. 23–25, with Remark 5.4 (printed p. 25 / PDF p. 26)

import Definitions.Def_GuanQinQDP_Restricted_Supplement_Model
open QAlgorithms QAlgorithms.Entanglement GuanQinQDP.Restricted
open scoped Matrix ComplexOrder

namespace GuanQinQDP.Restricted.Supplement

/-- Lemma 5.3 (Measure-and-prepare sandwich), Guan–Qin, STOC 2027 submission #1640, printed
p. 22 / PDF p. 23.

1. Let `Λ : M₂ → M₂` be completely positive and unital, and let `1 ≤ r` with
   `λ_max(Λ(N)) ≤ r λ_min(Λ(N))` for every `N ⪰ 0`. Then there is a measure-and-prepare map
   `T(N) = ∑_x Tr(τ_x N) F_x` (states `τ_x`, `F_x ⪰ 0`) with `Λ ⪯_CP T ⪯_CP g(r) Λ`.
2. No smaller coefficient depending only on `r` suffices: for every `r ≥ 1` and every `t < g(r)`
   there is a completely positive unital `Λ` satisfying the hypothesis with this `r` for which no
   measure-and-prepare `T` has `Λ ⪯_CP T ⪯_CP t Λ`. -/
theorem measure_prepare_sandwich :
    (∀ Λ : Matrix Qubit Qubit ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ, IsCompletelyPositive Λ → Λ 1 = 1 →
      ∀ r : ℝ, 1 ≤ r → SpectralRatioLe Λ r →
        ∃ T : Matrix Qubit Qubit ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ,
          IsMeasurePrepare T ∧ CPLe Λ T ∧ CPLe T (((gcost r : ℝ) : ℂ) • Λ)) ∧
    (∀ r : ℝ, 1 ≤ r → ∀ t : ℝ, t < gcost r →
      ∃ Λ : Matrix Qubit Qubit ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ,
        IsCompletelyPositive Λ ∧ Λ 1 = 1 ∧ SpectralRatioLe Λ r ∧
          ¬ ∃ T : Matrix Qubit Qubit ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ,
            IsMeasurePrepare T ∧ CPLe Λ T ∧ CPLe T ((t : ℂ) • Λ)) := by sorry

end GuanQinQDP.Restricted.Supplement
