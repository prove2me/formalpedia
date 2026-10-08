-- Prove2me | Theorems.Thm_HighDimCLT_MultBoot_remark_4_1
-- name    : HighDimCLT.MultBoot.remark_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:02.578987+00:00
-- url     : https://prove2.me/theorems/15b6d717-c0ee-408e-9d38-f94144484ce9
-- title:
--   Remark 4.1 = (38), pp. 2319, 2342 — ρ^MB_n(𝒜^re) ≤ CΔ̄_n^{1/3} log^{2/3} p on the event Δ_{n,r} ≤ Δ̄_n, C depending only on b
-- statement:
--   For every $b>0$ there is $C>0$, depending only on $b$, such that the following holds. Assume the standing setting with $n\ge4$, $p\ge3$ and condition (M.1). Then for every constant $\bar\Delta_n>0$, at every realization of the data on the event $\Delta_{n,r}\le\bar\Delta_n$, and for every hyperrectangle $A=\{w: a_j\le w_j\le b_j\ \forall j\}$ with $-\infty\le a_j\le b_j\le\infty$,
--   $$\big|P(S_n^{eX}\in A\mid X_1^n)-P(S_n^Y\in A)\big|\le C\,\bar\Delta_n^{1/3}\log^{2/3}p;$$
--   that is, $\rho_n^{MB}(\mathcal A^{re})\le C\bar\Delta_n^{1/3}\log^{2/3}p$.
--
--   This is the multiplier bootstrap theorem for hyperrectangles, the case most used in applications (simultaneous confidence bands, max-type tests).
--
--   **Formalization Note** "On the event" is read per realization: for every $\omega$ with $\Delta_{n,r}(X(\omega))\le\bar\Delta_n$ the bound holds for the bootstrap law at $X(\omega)$. The supremum over $\mathcal A^{re}$ is stated as a bound for every hyperrectangle; endpoints are extended reals.
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), p. 2319, Remark 4.1; p. 2342, App. E.2, display (38)

import Mathlib
import Definitions.Def_HighDimCLT_MultBoot_Setting

namespace HighDimCLT.MultBoot

open MeasureTheory ProbabilityTheory

universe u

/-- **Remark 4.1 = display (38)**, p. 2319 and App. E.2, p. 2342: under (M.1) there is `C > 0`
depending only on `b` such that for every constant `Δ̄_n > 0`, at every realization of the data
on the event `Δ_{n,r} ≤ Δ̄_n`,
`ρ^MB_n(𝒜^re) = sup_{A ∈ 𝒜^re} |P(S^{eX}_n ∈ A | X₁ⁿ) − P(S^Y_n ∈ A)| ≤ C Δ̄_n^{1/3} log^{2/3} p`. -/
theorem remark_4_1 : ∀ b : ℝ, 0 < b → ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n p : ℕ),
    4 ≤ n → 3 ≤ p → ∀ (X Y : Fin n → Ω → EuclideanSpace ℝ (Fin p)), Standing P X Y →
    VarFloor P X b → ∀ Δbar : ℝ, 0 < Δbar → ∀ ω : Ω, DeltaR (fun i => X i ω) P X ≤ Δbar →
    ∀ lo hi : Fin p → EReal, (∀ j, lo j ≤ hi j) →
      |(mbLaw (fun i => X i ω)).real (hyperrect lo hi)
          - P.real {ω' | normSum Y ω' ∈ hyperrect lo hi}|
        ≤ C * Δbar ^ (1 / 3 : ℝ) * Real.log p ^ (2 / 3 : ℝ) := by sorry

end HighDimCLT.MultBoot
