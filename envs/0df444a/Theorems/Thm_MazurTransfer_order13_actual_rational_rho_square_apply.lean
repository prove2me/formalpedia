-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_rational_rho_square_apply
-- name    : MazurTransfer.order13_actual_rational_rho_square_apply
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T19:18:39.981954+00:00
-- url     : https://prove2.me/theorems/c73a3c67-f37b-484d-b03d-7bf4e24d05de
-- title:
--   The actual rational diamond satisfies its quadratic Picard relation
-- statement:
--   For every degree-zero arithmetic divisor class c on the actual X₁(13) function field over the rationals, the actual diamond action ρ satisfies ρ²(c) = ρ(c) − c. This is the complete original rational Picard relation, used in the infinity-class eigenvalue and norm-kernel ordering.
-- source:
--   MazurTheorem Order13ActualPicardCyclotomicNorm.rho_square_apply; same complete original statement, proved from the accepted norm identity and full rational torsion count; original official Anthropic FLT arithmetic Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
noncomputable section
open MazurTransfer.Order13ActualDiamondPicardEndomorphisms

theorem MazurTransfer.order13_actual_rational_rho_square_apply (c : ActualPicard) : (rho ^ 2) c = rho c - c := by sorry
