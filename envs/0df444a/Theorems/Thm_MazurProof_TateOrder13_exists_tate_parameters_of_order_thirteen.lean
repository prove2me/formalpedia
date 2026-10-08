-- Prove2me | Theorems.Thm_MazurProof_TateOrder13_exists_tate_parameters_of_order_thirteen
-- name    : MazurProof.TateOrder13.exists_tate_parameters_of_order_thirteen
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T21:50:27.779777+00:00
-- url     : https://prove2.me/theorems/acfc34f8-c1fb-474e-8638-9b85f1e33a56
-- title:
--   exists tate parameters of order thirteen
-- statement:
--   An elliptic curve over the rationals with a point of exact order thirteen admits Tate normal-form parameters with nonzero first parameter satisfying the order-thirteen division-polynomial equation.
-- source:
--   51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.TateOrder13

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.TateOrder13
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_TateNFDivision_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_TateNormalFormBridge_p0
import Definitions.Def_MazurN13_KeystoneInterface
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_TateOrder13_p0

set_option autoImplicit false

open Polynomial
open scoped WeierstrassCurve.Affine
namespace MazurProof.TateOrder13
open Scratch.TateZ2xZ10Reduction
noncomputable section

theorem exists_tate_parameters_of_order_thirteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 13) :
    ∃ b c : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
        addOrderOf (tateOrigin b c) = 13 ∧
          b ≠ 0 ∧ TateNFDivision.F13 b c = 0 := by sorry
end
end MazurProof.TateOrder13
