-- Prove2me | Theorems.Thm_MasulloRH_unit_height_em_pointwise_ball_certificate
-- name    : MasulloRH.unit_height_em_pointwise_ball_certificate
-- status  : Open
-- author  : @WalrusPaul
-- created : 2026-11-22T19:06:25.400514+00:00
-- url     : https://prove2.me/theorems/458479ec-80ed-41ca-9e08-9f4753b887b0
-- title:
--   Pointwise Euler–Maclaurin ball certificates on a unit-height rectangle
-- statement:
--   For each point of the closed rectangle in the parent theorem, there is an in-rectangle rational center and a rational radius whose open ball contains that point. At that center some truncation parameters satisfy the strict Euler–Maclaurin certificate inequality of the parent. Both the center and the parameters may depend on the point. This is the unresolved local analytic estimate.
-- source:
--   Pointwise obligation extracted from https://prove2.me/theorems/fa0bbf43-2258-465f-95d2-56813214d210

import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Mathlib.Data.Rat.Cast.Order
set_option autoImplicit false
open Set

theorem MasulloRH.unit_height_em_pointwise_ball_certificate (n k : ℕ) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let R := Complex.reProdIm (Icc (1 / 2 + margin) 1)
      (Icc ((100000 : ℝ) + n + margin) ((100000 : ℝ) + n + 1))
    let M : ℚ := 16 * (100003 + n)
    let center (p : ℚ × ℚ) : ℂ := ⟨(p.1 : ℝ), (p.2 : ℝ)⟩
    let cert (p : ℚ × ℚ) (r : ℚ) := center p ∈ R ∧
      ∃ K N : ℕ, 1 ≤ K ∧ 1 ≤ N ∧
        let err : ℚ := ((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
          (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K))
        ((M * r + err : ℚ) : ℝ) < ‖ZetaReflection.EMHigh.emFinite K (center p) N‖
    ∀ s ∈ R, ∃ p r, cert p r ∧ dist s (center p) < (r : ℝ) := by sorry
