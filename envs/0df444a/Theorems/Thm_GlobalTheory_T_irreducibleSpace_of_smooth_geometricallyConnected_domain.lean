-- Prove2me | Theorems.Thm_GlobalTheory_T_irreducibleSpace_of_smooth_geometricallyConnected_domain
-- name    : GlobalTheory.T.irreducibleSpace_of_smooth_geometricallyConnected_domain
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:34:22.678163+00:00
-- url     : https://prove2.me/theorems/bff527ff-5f64-5f5a-a6ef-cb581c5690ce
-- title:
--   T: irreducible Space of smooth geometrically Connected domain
-- statement:
--   The T construction uses the irreducible Space of smooth geometrically Connected domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleSpaceOfSmoothOfGeometricallyConnectedStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleSpaceOfSmoothOfGeometricallyConnectedStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpaceOfSmoothOfGeometricallyConnected
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpaceOfSmoothOfGeometricallyConnectedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.irreducibleSpace_of_smooth_geometricallyConnected_domain : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))), Smooth G.hom → GeometricallyConnected G.hom → Nonempty G.left → IrreducibleSpace G.left := by sorry
