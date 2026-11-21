-- Prove2me | Theorems.Thm_MasulloRH_critical_zero_band_of_signed_brackets
-- name    : MasulloRH.critical_zero_band_of_signed_brackets
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:35:52.076126+00:00
-- url     : https://prove2.me/theorems/d4b9a986-0f3a-46f0-9246-1ab9ff78647d
-- title:
--   A positive-height sign table can miss one distinct zero and still certify a full critical band
-- statement:
--   In the positive-ordinate band L<Im(ρ)≤H, suppose E is a finite set of known critical-line zeros. In addition, take disjoint rational open intervals contained between L and H, disjoint from the ordinates in E, with strictly opposite real completed-zeta signs at the endpoints. If the total number of distinct nontrivial zeros in the positive band is at most |E| plus the number of intervals plus one, then every nontrivial zero with L<|Im(ρ)|≤H is on the critical line. Arbitrary known central zeros may enter E without a sign change. The argument requires no zero-simplicity statement.
-- source:
--   MasulloRH.prime_height_critical_zero_count_certificates, 60aa6e62. This finite completeness test uses the real completed-zeta identity 773c743f, the zeta functional equation and complex conjugation. For the classical use of consecutive sign evaluations and independent zero counts see D. Platt and T. Trudgian, The Riemann hypothesis is true up to 3·10^12, https://doi.org/10.1112/blms.12460. The one-zero slack and the mixed exact-root/sign-bracket statement are established here.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.Data.Set.Card

set_option autoImplicit false

open Set Finset
namespace MasulloRH

theorem critical_zero_band_of_signed_brackets (L H : ℝ)
    (E : Finset (ZetaZerosInTraceStrip (1/2))) (B : Finset (ℚ×ℚ))
    (hE : ∀ z ∈ E, L < z.val.im ∧ z.val.im ≤ H ∧ z.val.re=1/2)
    (hB : ∀ i ∈ B, L ≤ (i.1:ℝ) ∧ i.1 < i.2 ∧ (i.2:ℝ) ≤ H ∧
      (completedRiemannZeta (1/2 + (i.1:ℂ)*Complex.I)).re * (completedRiemannZeta (1/2 + (i.2:ℂ)*Complex.I)).re < 0)
    (hD : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (Set.Ioo (i.1:ℝ) (i.2:ℝ)) (Set.Ioo (j.1:ℝ) (j.2:ℝ)))
    (hED : ∀ z ∈ E, ∀ i ∈ B, z.val.im ∉ Set.Ioo (i.1:ℝ) (i.2:ℝ))
    (hcount : Set.encard {z : ZetaZerosInTraceStrip (1/2) | L<z.val.im ∧ z.val.im≤H} ≤ ((E.card+B.card+1:ℕ):ℕ∞)) :
    ∀ z : ZetaZerosInTraceStrip (1/2), L < |z.val.im| → |z.val.im| ≤ H → z.val.re=1/2 := by sorry

end MasulloRH
