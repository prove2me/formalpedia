-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isScalarTower_residueField
-- name    : GroundTheory.LocalField.isScalarTower_residueField
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:15:13.241947+00:00
-- url     : https://prove2.me/theorems/0c651b53-305f-4781-835e-08318524e4e6
-- title:
--   Local Field: is Scalar Tower residue Field
-- statement:
--   The Local Field construction uses the is Scalar Tower residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedHensel.lean#L43-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedHensel.lean#L43-L56

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField

theorem GroundTheory.LocalField.isScalarTower_residueField (K E L : Type*) [Field K] [ValuativeRel K] [Field E]
    [ValuativeRel E] [Field L] [ValuativeRel L] [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L] [ValuativeExtension K E] [ValuativeExtension E L]
    [ValuativeExtension K L] [Algebra 𝓀[K] 𝓀[E]] [Algebra 𝓀[E] 𝓀[L]] [Algebra 𝓀[K] 𝓀[L]]
    (h₁ : ∀ x : 𝒪[K], algebraMap 𝓀[K] 𝓀[E] (residue 𝒪[K] x) =
      residue 𝒪[E] (algebraMap 𝒪[K] 𝒪[E] x))
    (h₂ : ∀ x : 𝒪[E], algebraMap 𝓀[E] 𝓀[L] (residue 𝒪[E] x) =
      residue 𝒪[L] (algebraMap 𝒪[E] 𝒪[L] x))
    (h₃ : ∀ x : 𝒪[K], algebraMap 𝓀[K] 𝓀[L] (residue 𝒪[K] x) =
      residue 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] x)) :
    IsScalarTower 𝓀[K] 𝓀[E] 𝓀[L] := by sorry
