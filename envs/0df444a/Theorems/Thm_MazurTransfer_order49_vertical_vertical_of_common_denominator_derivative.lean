-- Prove2me | Theorems.Thm_MazurTransfer_order49_vertical_vertical_of_common_denominator_derivative
-- name    : MazurTransfer.order49_vertical_vertical_of_common_denominator_derivative
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T04:22:15.210346+00:00
-- url     : https://prove2.me/theorems/6868d1fe-3ee2-4840-9778-dab517f5f376
-- title:
--   Exact vertical identity from a common-denominator derivative certificate
-- statement:
--   The full original scalar derivative-to-vertical-coordinate identity, universally quantified over the original rational scalar parameters and retaining every polynomial identity and nonzero-denominator hypothesis.
--
--   This supplies an exact original derivative identity used in the order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original _private.MazurTorsion.Kubert.OrderSevenIsogenyDoublingDerivative.0.MazurTorsion.Kubert.OrderSevenDoublingDerivative.vertical_of_common_denominator_derivative. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
open Polynomial

theorem MazurTransfer.order49_vertical_vertical_of_common_denominator_derivative {A Ad B Bd H Hd Kh Khd Q Qd Ht Htd Nh R Rt K N : ℚ}
    (hA : A = B) (hAd : Ad = Bd)
    (hden : H * Kh ^ 2 = Q * Ht)
    (hdendot : Hd * Kh ^ 2 + 2 * H * Kh * Khd = Qd * Ht + Q * Htd)
    (hleft : Ad * H * Kh - A * (Hd * Kh + 2 * H * Khd) = 2 * Nh * R)
    (hright : Bd * Q * Ht - B * (Qd * Ht + Q * Htd) = 2 * Rt * K * N)
    (hKh : Kh = K * N) (hK : K ≠ 0) (hN : N ≠ 0) :
    Nh * R = Rt := by sorry
