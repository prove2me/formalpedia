-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_finite_support_torusResidue
-- name    : GroundTheory.Global.Elliptic.finite_support_torusResidue
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:38:48.447358+00:00
-- url     : https://prove2.me/theorems/74b3edff-ff1f-4029-9aff-29b48d9d0858
-- title:
--   Elliptic: finite support torus Residue
-- statement:
--   The Elliptic construction uses the finite support torus Residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticDegree.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticDegree.lean#L64-L68

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

theorem GroundTheory.Global.Elliptic.finite_support_torusResidue {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    (Function.support (torusResidue L f)).Finite := by sorry
