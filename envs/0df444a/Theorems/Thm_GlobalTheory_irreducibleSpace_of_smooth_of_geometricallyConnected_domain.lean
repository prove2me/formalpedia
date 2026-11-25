-- Prove2me | Theorems.Thm_GlobalTheory_irreducibleSpace_of_smooth_of_geometricallyConnected_domain
-- name    : GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:56:20.415815+00:00
-- url     : https://prove2.me/theorems/86507187-1b77-48de-8851-1ba491902799
-- title:
--   Global Theory: irreducible Space of smooth of geometrically Connected domain
-- statement:
--   The Global Theory construction uses the irreducible Space of smooth of geometrically Connected domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleSpaceOfSmoothOfGeometricallyConnected.lean#L9-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleSpaceOfSmoothOfGeometricallyConnected.lean#L9-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpaceOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpaceOfSmoothOfGeometricallyConnected
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
open GlobalTheory

theorem GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain :
    ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))), Smooth G.hom →
      GeometricallyConnected G.hom → Nonempty G.left → IrreducibleSpace G.left := by sorry
