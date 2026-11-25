-- Prove2me | Theorems.Thm_GlobalTheory_homology_of_free_complex_of_isFiniteLength
-- name    : GlobalTheory.homology_of_free_complex_of_isFiniteLength
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:49.146021+00:00
-- url     : https://prove2.me/theorems/b18441ee-a009-4485-92cd-ca950edd7dfd
-- title:
--   Global Theory: homology of free complex of is Finite Length
-- statement:
--   The Global Theory construction uses the homology of free complex of is Finite Length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L272-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L272-L327

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing
open GlobalTheory
open FiniteLengthComplex

theorem GlobalTheory.homology_of_free_complex_of_isFiniteLength :
    ∀ (O : Type) [CommRing O] [IsRegularLocalRing O] (g : ℕ), ringKrullDim O = g →
      ∀ C : CochainComplex (ModuleCat.{0} O) ℕ,
        (∀ i, Module.Free O (C.X i) ∧ Module.Finite O (C.X i)) → (∀ i, g < i → IsZero (C.X i)) →
        (∀ i, IsFiniteLength O (C.homology i)) →
        Nonempty ((Module.Dual O (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[O]
          IsLocalRing.ResidueField O) →
        (∀ i, i ≠ g → IsZero (C.homology i)) ∧ Module.length O (C.homology g) = 1 := by sorry
