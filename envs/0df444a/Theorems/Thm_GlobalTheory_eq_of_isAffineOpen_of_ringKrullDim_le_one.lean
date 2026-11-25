-- Prove2me | Theorems.Thm_GlobalTheory_eq_of_isAffineOpen_of_ringKrullDim_le_one
-- name    : GlobalTheory.eq_of_isAffineOpen_of_ringKrullDim_le_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:45:38.629843+00:00
-- url     : https://prove2.me/theorems/adb6f256-0026-41be-bb4b-37cb2afe618d
-- title:
--   Global Theory: eq of is Affine Open of ring Krull Dim le one
-- statement:
--   The Global Theory construction uses the eq of is Affine Open of ring Krull Dim le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqOfIsAffineOpenOfRingKrullDimLeOne.lean#L20-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqOfIsAffineOpenOfRingKrullDimLeOne.lean#L20-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqOfIsAffineOpenOfRingKrullDimLeOne
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory

theorem GlobalTheory.eq_of_isAffineOpen_of_ringKrullDim_le_one (X : Scheme.{0}) [IsLocallyNoetherian X]
    [X.IsSeparated] (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (V V' : X.Opens)
    (hV : IsAffineOpen V) (hle : V ≤ V')
    (h : ∀ z ∈ V', ringKrullDim (X.presheaf.stalk z) ≤ 1 → z ∈ V) : V' = V := by sorry
