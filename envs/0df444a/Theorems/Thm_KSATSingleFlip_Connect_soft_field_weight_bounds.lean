-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_weight_bounds
-- name    : KSATSingleFlip.Connect.soft_field_weight_bounds
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:10:50.807571+00:00
-- url     : https://prove2.me/theorems/27142639-8288-40e5-a7c5-d5678b14097b
-- title:
--   Soft-field test functions satisfy 0 ≤ g ≤ f ≤ 1
-- statement:
--   For q in [0,1], the soft-field test functions f(q)=2√(q(1−q)) and g(q)=2(√q+√(1−q)−1) obey 0 ≤ g(q) ≤ f(q) ≤ 1. The comparison is used in the Poisson comparison and potential bounds of Section 4.1.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Section 4.1 and Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect

theorem KSATSingleFlip.Connect.soft_field_weight_bounds (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ gW q ∧ gW q ≤ fW q ∧ fW q ≤ 1 := by sorry
