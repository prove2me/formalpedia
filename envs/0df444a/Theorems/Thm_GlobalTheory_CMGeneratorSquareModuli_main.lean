-- Prove2me | Theorems.Thm_GlobalTheory_CMGeneratorSquareModuli_main
-- name    : GlobalTheory.CMGeneratorSquareModuli.main
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:03:22.217268+00:00
-- url     : https://prove2.me/theorems/2cfb8552-c879-4f26-a7d5-df8d8630fa1a
-- title:
--   CMGenerator Square Moduli: main
-- statement:
--   The CMGenerator Square Moduli construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CmGeneratorSqQuadraticEq.lean#L28-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CmGeneratorSqQuadraticEq.lean#L28-L48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmGeneratorSqQuadraticEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CMGeneratorSquareModuli
open NumberField

theorem GlobalTheory.CMGeneratorSquareModuli.main : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {a : NumberField.RingOfIntegers E},
    a ∈ Algebra.adjoin ℤ ({ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H} : Set (NumberField.RingOfIntegers E)) →
    ∃ u v : ℤ, a = (u : NumberField.RingOfIntegers E) + (v : NumberField.RingOfIntegers E) * ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H := by sorry
