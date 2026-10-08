-- Prove2me | Theorems.Thm_McLeishCLT_MDA_trunc_isMDA
-- name    : McLeishCLT.MDA.trunc_isMDA
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:31:58.471156+00:00
-- url     : https://prove2.me/theorems/1953bd43-5d4b-46af-a3b9-b2a744ab5867
-- title:
--   p. 622, proof of (2.3) — Z_{n,j} = X_{n,j} I(Σ_{k<j} X²_{n,k} ≤ 2) is again a martingale difference array
-- statement:
--   Let $\{X_{n,i}\}$ be a martingale difference array with respect to row-wise filtrations $\{\mathcal F_{n,i};\ 0\le i\le k_n\}$ on a probability space: each $X_{n,i}$ is $\mathcal F_{n,i}$-measurable and integrable, and $E(X_{n,i}\mid\mathcal F_{n,i-1})=0$ a.s. Define
--   $$Z_{n,j}=X_{n,j}\,I\Big(\sum_{k=1}^{j-1}X_{n,k}^2\le2\Big).$$
--   Then $\{Z_{n,j}\}$ is also a martingale difference array with respect to the same σ-fields.
--
--   This is the first observation of the proof of Theorem (2.3): the truncation by the running sum of squares preserves the martingale property and makes the products $T_n$ well behaved.
-- source:
--   McLeish, Dependent central limit theorems and invariance principles, Ann. Probab. 2 (1974), p. 622, proof of Theorem (2.3), sentence before (2.5)

import Mathlib
import Definitions.Def_McLeishCLT_MDA_Setting

namespace McLeishCLT.MDA

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- p. 622, proof of (2.3): the truncated array `Z_{n,j}` is again a martingale difference array. -/
theorem trunc_isMDA {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : ℕ → Filtration ℕ m0) (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ)
    (hmda : IsMDA P ℱ k X) :
    IsMDA P ℱ k (trunc X) := by sorry

end McLeishCLT.MDA
