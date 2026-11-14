-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_weight_lower_bound
-- name    : KSATSingleFlip.Connect.soft_field_weight_lower_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:33:42.87716+00:00
-- url     : https://prove2.me/theorems/4999bb33-d4b4-47fc-b17e-141579a5c64e
-- title:
--   Sharp lower comparison between the soft-field weights
-- statement:
--   For q in [0,1], g(q) ≥ 2(√2−1)f(q). Together with g ≤ f this is the exact pointwise comparison used in Section 4.1 to compare the soft-field potential and total mass.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Section 4.1 immediately before Definition 4.2, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect

theorem KSATSingleFlip.Connect.soft_field_weight_lower_bound (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) : c0*fW q ≤ gW q := by sorry
