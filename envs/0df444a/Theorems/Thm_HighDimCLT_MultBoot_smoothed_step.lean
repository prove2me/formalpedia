-- Prove2me | Theorems.Thm_HighDimCLT_MultBoot_smoothed_step
-- name    : HighDimCLT.MultBoot.smoothed_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:40:34.476992+00:00
-- url     : https://prove2.me/theorems/c5385064-1046-4661-8ba7-0ee59fe727e5
-- title:
--   App. E.2, p. 2342 — |P(S^{eX}_n ≤ y − φ⁻¹ | X₁ⁿ) − P(S^Y_n ≤ y − φ⁻¹)| ≤ C{φ⁻¹ log^{1/2} p + (φ² + βφ)Δ_{n,r}}, β = φ log p
-- statement:
--   For every $b>0$ there is $C>0$, depending only on $b$, such that the following holds. Assume the standing setting with $n\ge4$, $p\ge3$ and condition (M.1): $n^{-1}\sum_i\mathrm E[X_{ij}^2]\ge b$ for all $j$. Then for every realization of the data, every $y\in\mathbb R^p$ and every $\phi>0$, with $\beta=\phi\log p$,
--   $$\big|P(S_n^{eX}\le y-\phi^{-1}\mid X_1^n)-P(S_n^Y\le y-\phi^{-1})\big|\le C\big\{\phi^{-1}\log^{1/2}p+(\phi^2+\beta\phi)\Delta_{n,r}\big\}.$$
--
--   This is the smoothed comparison step of the proof of (39); optimizing over $\phi$ yields (39).
--
--   **Formalization Note** $P(\cdot\mid X_1^n)$ is the bootstrap law at the realization $X(\omega)$, for every $\omega$. The page does not restrict $\phi$; the statement is for every $\phi>0$. The proof's convention says $C$ depends on $a,b,d$, but this step uses only (M.1) and Lemma A.1, so $C$ is chosen after $b$ alone (as in Remark 4.1).
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), p. 2342, App. E.2, Proof of Theorem 4.1, display after "as in Step 2 of the proof of Lemma 5.1"

import Mathlib
import Definitions.Def_HighDimCLT_MultBoot_Setting

namespace HighDimCLT.MultBoot

open MeasureTheory ProbabilityTheory

universe u

/-- **Smoothed comparison step**, App. E.2, p. 2342: under (M.1) there is `C > 0` depending
only on `b` such that for every realization of the data, every `y ∈ ℝ^p` and every `φ > 0`,
with `β = φ log p`,
`|P(S^{eX}_n ≤ y − φ^{-1} | X₁ⁿ) − P(S^Y_n ≤ y − φ^{-1})| ≤ C(φ^{-1} log^{1/2} p + (φ² + βφ)Δ_{n,r})`. -/
theorem smoothed_step : ∀ b : ℝ, 0 < b → ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n p : ℕ),
    4 ≤ n → 3 ≤ p → ∀ (X Y : Fin n → Ω → EuclideanSpace ℝ (Fin p)), Standing P X Y →
    VarFloor P X b → ∀ (ω : Ω) (y : EuclideanSpace ℝ (Fin p)) (φ : ℝ), 0 < φ →
      |(mbLaw (fun i => X i ω)).real {w | ∀ j, w j ≤ y j - φ⁻¹}
          - P.real {ω' | ∀ j, normSum Y ω' j ≤ y j - φ⁻¹}|
        ≤ C * (φ⁻¹ * Real.sqrt (Real.log p)
          + (φ ^ 2 + (φ * Real.log p) * φ) * DeltaR (fun i => X i ω) P X) := by sorry

end HighDimCLT.MultBoot
