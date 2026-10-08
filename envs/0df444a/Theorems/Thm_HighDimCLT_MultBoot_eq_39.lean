-- Prove2me | Theorems.Thm_HighDimCLT_MultBoot_eq_39
-- name    : HighDimCLT.MultBoot.eq_39
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:51.134084+00:00
-- url     : https://prove2.me/theorems/d8c4b28b-8bcc-44ba-b232-87b4d181e1d4
-- title:
--   (39), p. 2342 — sup_y |P(S^{eX}_n ≤ y | X₁ⁿ) − P(S^Y_n ≤ y)| ≤ CΔ_{n,r}^{1/3} log^{2/3} p
-- statement:
--   For every $b>0$ there is $C>0$, depending only on $b$, such that the following holds. Assume the standing setting with $n\ge4$, $p\ge3$ and condition (M.1). Then for every realization of the data and every $y\in\mathbb R^p$,
--   $$\big|P(S_n^{eX}\le y\mid X_1^n)-P(S_n^Y\le y)\big|\le C\,\Delta_{n,r}^{1/3}\log^{2/3}p,$$
--   where $\Delta_{n,r}=\max_{j,k}|\widehat\Sigma_{jk}-\Sigma_{jk}|$ is computed from the realization; equivalently $\varrho_n^{MB}=\sup_y|\cdots|\le C\Delta_{n,r}^{1/3}\log^{2/3}p$.
--
--   This is the bootstrap bound for lower orthants, from which (38) for hyperrectangles follows.
--
--   **Formalization Note** The supremum over $y$ is stated as a bound for every $y$. $P(\cdot\mid X_1^n)$ is the bootstrap law at $X(\omega)$, for every $\omega$. $C$ is chosen after $b$ alone (the proof uses only (M.1); Remark 4.1 states that $C$ depends only on $b$).
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), p. 2342, App. E.2, display (39)

import Mathlib
import Definitions.Def_HighDimCLT_MultBoot_Setting

namespace HighDimCLT.MultBoot

open MeasureTheory ProbabilityTheory

universe u

/-- **Display (39)**, App. E.2, p. 2342: under (M.1) there is `C > 0` depending only on `b`
such that, for every realization of the data,
`sup_y |P(S^{eX}_n ≤ y | X₁ⁿ) − P(S^Y_n ≤ y)| ≤ C Δ_{n,r}^{1/3} log^{2/3} p`. -/
theorem eq_39 : ∀ b : ℝ, 0 < b → ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n p : ℕ),
    4 ≤ n → 3 ≤ p → ∀ (X Y : Fin n → Ω → EuclideanSpace ℝ (Fin p)), Standing P X Y →
    VarFloor P X b → ∀ (ω : Ω) (y : EuclideanSpace ℝ (Fin p)),
      |(mbLaw (fun i => X i ω)).real {w | ∀ j, w j ≤ y j}
          - P.real {ω' | ∀ j, normSum Y ω' j ≤ y j}|
        ≤ C * DeltaR (fun i => X i ω) P X ^ (1 / 3 : ℝ) * Real.log p ^ (2 / 3 : ℝ) := by sorry

end HighDimCLT.MultBoot
