-- Prove2me | Theorems.Thm_MasulloRH_compensated_resolvent_defect_low_high_split
-- name    : MasulloRH.compensated_resolvent_defect_low_high_split
-- status  : Open
-- author  : @ibecca
-- created : 2026-11-22T00:26:29.218088+00:00
-- url     : https://prove2.me/theorems/1b39c093-ef5a-4b28-95db-9cc637c7997c
-- title:
--   Finite low-height and summable high-height split of the compensated trace defect
-- statement:
--   Fix $0<\alpha<1/2$ and assume the explicit compensated-resolvent estimate for every zero-height pair with $\gamma^2\ge36$. The remaining spectral calculation is required to split the regularized-trace defect into two honest summable pieces. It must produce a finite set $F$ containing every zero with $|\operatorname{Im}\rho|^2<36$, together with nonnegative families $f_0$ and $f_\infty$ such that $f_0$ is supported on $F$, $f_\infty$ vanishes on $F$, both families are summable, and
--
--   $$
--   \operatorname{Re}\bigl(\mathrm{RHS}_{\alpha}(3)-\mathrm{RHS}_{1/2}(3)\bigr)
--   =\sum_{\rho}f_0(\rho)+\sum_{\rho}f_\infty(\rho).
--   $$
--
--   The finite part records the low-height bookkeeping, including any boundary convention at $|\operatorname{Im}\rho|^2=36$; the second part is the high-height series to which the compensated kernel estimate and the tail bounds apply. This is a decomposition of the Masullo spectral obligation itself. It does not assume the Riemann hypothesis, use a generic RH theorem, or import the Alpöge--Claude formalization.
-- source:
--   Masullo, The Music of the Primes, §§1.4.2–1.4.5 and Theorem 12.5.1.1 (20 November 2026 draft), with the Masullo-native compensated-resolvent strategy recorded in the mission discussion.

import Definitions.Def_MasulloRH_RegularizedTrace
open MasulloRH

theorem MasulloRH.compensated_resolvent_defect_low_high_split
    (α : ℝ) (hα : 0 < α) (hsmall : α < 1 / 2)
    (hkernel :
      ∀ (β γ T : ℝ), 0 ≤ β → β ≤ 1 → 36 ≤ γ ^ 2 →
        let a := 3 - β
        let b := 5 / 2 - β
        let c0 := a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2)
        let k := a / (a ^ 2 + (T - γ) ^ 2) - b / (b ^ 2 + γ ^ 2) + 8 * c0
        0 < k ∧ a / (a ^ 2 + (T - γ) ^ 2) ≤ k) :
    ∃ F : Set (ZetaZerosInTraceStrip (1 / 2)),
      F.Finite ∧
      (∀ ρ, |ρ.val.im| ^ 2 < 36 → ρ ∈ F) ∧
      ∃ fLow fHigh : ZetaZerosInTraceStrip (1 / 2) → ℝ,
        (∀ ρ, 0 ≤ fLow ρ) ∧
        (∀ ρ, 0 ≤ fHigh ρ) ∧
        (∀ ρ, ρ ∉ F → fLow ρ = 0) ∧
        (∀ ρ, ρ ∈ F → fHigh ρ = 0) ∧
        Summable fLow ∧ Summable fHigh ∧
        (regularizedTraceRHS α 3).re - (regularizedTraceRHS (1 / 2) 3).re =
          (∑' ρ, fLow ρ) + ∑' ρ, fHigh ρ := by sorry
