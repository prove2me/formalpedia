-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_finsum_toNat_torusOrder_sub_const
-- name    : GroundTheory.Global.Elliptic.finsum_toNat_torusOrder_sub_const
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:19.809969+00:00
-- url     : https://prove2.me/theorems/240b3faf-3bb9-41b4-912f-bcaf57ddf453
-- title:
--   Elliptic: finsum to Nat torus Order sub const
-- statement:
--   The Elliptic construction uses the finsum to Nat torus Order sub const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticDegree.lean#L154-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticDegree.lean#L154-L188

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

theorem GroundTheory.Global.Elliptic.finsum_toNat_torusOrder_sub_const {f : ℂ → ℂ} (hf : IsEllipticFunction L f) (c : ℂ) :
    ∑ᶠ x : Torus L, (torusOrder L (fun z ↦ f z - c) x).toNat = degree L f := by sorry
