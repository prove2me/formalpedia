-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_residue_logDeriv_eq_untopD
-- name    : GroundTheory.Global.Elliptic.residue_logDeriv_eq_untopD
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:38:34.901464+00:00
-- url     : https://prove2.me/theorems/dd00a840-4ed2-4a52-ac91-22f9cc5752e9
-- title:
--   Elliptic: residue log Deriv eq untop D
-- statement:
--   The Elliptic construction uses the residue log Deriv eq untop D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticDegree.lean#L42-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticDegree.lean#L42-L58

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticResidues
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}

theorem GroundTheory.Global.Elliptic.residue_logDeriv_eq_untopD {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) :
    residue (logDeriv f) z = (((meromorphicOrderAt f z).untopD 0 : ℤ) : ℂ) := by sorry
