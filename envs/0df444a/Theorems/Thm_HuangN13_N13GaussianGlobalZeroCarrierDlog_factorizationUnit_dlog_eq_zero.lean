-- Prove2me | Theorems.Thm_HuangN13_N13GaussianGlobalZeroCarrierDlog_factorizationUnit_dlog_eq_zero
-- name    : HuangN13.N13GaussianGlobalZeroCarrierDlog.factorizationUnit_dlog_eq_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T07:42:35.480298+00:00
-- url     : https://prove2.me/theorems/26f506c2-2d78-4f99-b6d8-71e0c2e50455
-- title:
--   The unit factor of a normalized Kummer square has zero ramified logarithm
-- statement:
--   If the normalized Kummer integer of a low-degree representative D factors as εy² in the integral order, then ε, transported to the normalization order, has zero first ramified logarithm.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source: https://github.com/xiangyazi24/FLT/blob/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof/N13GaussianGlobalZeroCarrierDlog.lean; exact flattened unit7, lines2676-2743, source-command SHA-256 de57f7976508c38a3a1d12241f1118bfbc8d68f78251e37c209708f4b3f70102. Original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13GaussianCubicField_integralClosure_eq_adjoin
import Theorems.Thm_MazurProof_N13GaussianCubicField_minpoly_alpha
import Theorems.Thm_MazurProof_N13GaussianGlobalReductionTwo_shiftedTheta_root_h
import Theorems.Thm_MazurProof_N13GaussianNamedUnitTransport_orderToGaussian_apply
import Theorems.Thm_MazurProof_N13LocalDlogRegimes_gaussianIDual_sq
import Theorems.Thm_MazurProof_N13LocalDlogRegimes_gaussian_cubic_jet_relation
import Definitions.Def_HuangN13_GaussianUnitLogCore

set_option autoImplicit false
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL MazurProof.N13GaussianNamedUnitTransport.fieldLg

theorem HuangN13.N13GaussianGlobalZeroCarrierDlog.factorizationUnit_dlog_eq_zero
    (D : MazurProof.N13GaussianGlobalZeroCarrierDlog.LowRep)
    (ε : MazurProof.N13GaussianGlobalZeroCarrierDlog.Oiˣ) (y : MazurProof.N13GaussianGlobalZeroCarrierDlog.Oi)
    (hxy :
      MazurProof.N13GlobalKummerNormalization.normalizedKummerInteger D =
        (ε : MazurProof.N13GaussianGlobalZeroCarrierDlog.Oi) * y ^ 2) :
    MazurProof.N13GaussianNamedUnitSquareclasses.globalDlogAdd
        (Additive.ofMul
          (Units.map
            MazurProof.N13GaussianNormalizationOrderTransport.normalizationOrderEquiv.toMonoidHom
            ε)) = 0 := by sorry
