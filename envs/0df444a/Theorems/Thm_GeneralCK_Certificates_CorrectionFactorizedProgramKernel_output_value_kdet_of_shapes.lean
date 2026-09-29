-- Prove2me | Theorems.Thm_GeneralCK_Certificates_CorrectionFactorizedProgramKernel_output_value_kdet_of_shapes
-- name    : GeneralCK.Certificates.CorrectionFactorizedProgramKernel.output_value_kdet_of_shapes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T22:56:13.408746+00:00
-- url     : https://prove2.me/theorems/c5bb406f-6ffd-40ce-95f5-6aa94448c1ae
-- title:
--   Program output for the factored determinant kernel
-- statement:
--   Any instruction list with the same operation shapes as the correction kernel program evaluates register $0$ to the natural-coordinate kernel $k_{\rm det}$ along the affine segment in the two ratio coordinates. The interval precision and proposed interval data do not affect this real-valued identity.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/CorrectionFactorizedProgramKernel.lean#L323-L329

import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.CorrectionFactorizedProgramKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open BivariateJetProgram (zeroBox zeroJet)
open BivariateProvedProgram

theorem GeneralCK.Certificates.CorrectionFactorizedProgramKernel.output_value_kdet_of_shapes {p : ℕ} (program : List (Instruction p))
    (h : shapes program = shapes kernelProgram) (ac zc a z t : ℝ) :
    ((finalJets program (inputJets ac zc a z)).getD 0 zeroJet).value t =
      Correction.Natural.kdet (ac+t*(a-ac)) ((ac+t*(a-ac))+(zc+t*(z-zc))*(1/2-(ac+t*(a-ac)))) := by sorry
