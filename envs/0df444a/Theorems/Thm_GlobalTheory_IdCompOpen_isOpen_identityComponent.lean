-- Prove2me | Theorems.Thm_GlobalTheory_IdCompOpen_isOpen_identityComponent
-- name    : GlobalTheory.IdCompOpen.isOpen_identityComponent
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:50:16.728907+00:00
-- url     : https://prove2.me/theorems/4db01bf3-1565-4a5a-bec4-89ba355c8a80
-- title:
--   Id Comp Open: is Open identity Component
-- statement:
--   The Id Comp Open construction uses the is Open identity Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenIdentityComponentsSmoothGroupScheme.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenIdentityComponentsSmoothGroupScheme.lean#L48-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOpenNbhdSectionFibreIsPreirreducibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSndImageMulMemOpenGroupSchemeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemUnitComponentMulMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIdentityComponentsOfMulInvStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfLocallyClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableUnderGeneralizationSectionComponentsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenIdentityComponentsSmoothGroupScheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IdCompOpen

theorem GlobalTheory.IdCompOpen.isOpen_identityComponent : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → IsOpen {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by sorry
