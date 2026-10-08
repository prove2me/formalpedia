-- Prove2me | Theorems.Thm_MinRankRecovery_RandomRIP_nearly_isometric_rip
-- name    : MinRankRecovery.RandomRIP.nearly_isometric_rip
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:52.554968+00:00
-- url     : https://prove2.me/theorems/048fe884-e6c5-4104-a653-3eab3b4fe33c
-- title:
--   Theorem 4.2 — nearly isometric random maps have δ_r ≤ δ with probability ≥ 1 − e^(−c₁p) once p ≥ c₀r(m+n)log(mn)
-- statement:
--   Fix $0<\delta<1$. There are constants $c_0,c_1>0$, depending only on $\delta$, with the following property. Let $1\le r\le m\le n$ with $mn\ge 2$, let $p$ satisfy
--   $$p\ \ge\ c_0\, r\,(m+n)\log(mn),$$
--   and let $\mathcal A:\mathbb R^{m\times n}\to\mathbb R^p$ be a nearly isometrically distributed random linear map. Then
--   $$\mathbb P\big(\delta_r(\mathcal A)\le\delta\big)\ \ge\ 1-e^{-c_1 p},$$
--   where $\delta_r(\mathcal A)$ is the $r$-restricted isometry constant.
--
--   This is the paper's main probabilistic result: on the order of $r(m+n)\log(mn)$ random linear measurements of an $m\times n$ matrix suffice for the restricted isometry property on rank-$r$ matrices, with overwhelming probability. Combined with the paper's deterministic recovery theorem it shows that nuclear norm minimization recovers low-rank matrices from that many random measurements.
--
--   **Formalization Note**
--   1. **Correction** $mn\ge2$: at $m=n=r=1$ one has $\log(mn)=0$, the sample condition holds for every $p$, and the map $X\mapsto\xi X$ with $\xi^2\in\{0,2\}$ equally likely ($p=1$) is nearly isometric while $\delta_1=\big||\xi|-1\big|\in\{1,\sqrt2-1\}$, so the printed statement fails there for every $c_0,c_1$.
--   2. $c_0,c_1$ are quantified before $m,n,p,r$, the probability space, the map and its constant $\gamma$, matching "depending only on $\delta$".
--   3. "For every $1\le r\le m$" is posed with the paper's standing convention $m\le n$ (Definition 3.1).
--   4. The event $\{\delta_r(\mathcal A)\le\delta\}$ need not be measurable, so the statement bounds the (outer) probability of the failure event $\{\delta_r(\mathcal A)>\delta\}$ by $e^{-c_1p}$; for a measurable event this is the printed bound.
--   5. $\log$ is the natural logarithm; a change of base is absorbed in $c_0$.
-- source:
--   Recht, Fazel & Parrilo, arXiv:0706.4138v1, Theorem 4.2, p. 15

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core
import Definitions.Def_MinRankRecovery_Recovery_ripConst
import Definitions.Def_MinRankRecovery_RandomRIP_NearlyIsometric

open HighDimStat.MatrixRank MeasureTheory

namespace MinRankRecovery.RandomRIP

/-- Theorem 4.2, p. 15 (with `mn ≥ 2`): fix `0 < δ < 1`. There are constants `c₀, c₁ > 0`
depending only on `δ` such that for all dimensions `1 ≤ r ≤ m ≤ n` with `mn ≥ 2`, every
`p ≥ c₀ r (m + n) log(mn)` and every nearly isometric random map `A : ℝ^{m×n} → ℝᵖ`,
`δ_r(A) ≤ δ` with probability at least `1 − exp(−c₁ p)`; stated in complement form, the
(outer) probability of `δ_r(A) > δ` is at most `exp(−c₁ p)`. -/
theorem nearly_isometric_rip (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ (m n p r : ℕ), 1 ≤ r → r ≤ m → m ≤ n → 2 ≤ m * n →
        c₀ * r * ((m : ℝ) + n) * Real.log ((m : ℝ) * n) ≤ p →
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (Xs : Ω → Fin p → Matrix (Fin m) (Fin n) ℝ), IsNearlyIsometric μ Xs →
          μ {ω | δ < MinRankRecovery.Recovery.ripConst (Xs ω) r} ≤ ENNReal.ofReal (Real.exp (-(c₁ * p))) := by sorry

end MinRankRecovery.RandomRIP
