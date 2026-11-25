-- Prove2me | Theorems.Thm_GlobalTheory_HL_GlobalOrbits_smul_eq_of_le
-- name    : GlobalTheory.HL.GlobalOrbits.smul_eq_of_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:36:33.745512+00:00
-- url     : https://prove2.me/theorems/6bd43eb8-2cda-5adc-84fb-d282067f213b
-- title:
--   Global Orbits: smul eq of le
-- statement:
--   The Global Orbits construction uses the smul eq of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GlobalHermitianFramesTermsOrbitsLocal.lean#L70-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GlobalHermitianFramesTermsOrbitsLocal.lean#L70-L89

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NumberFieldLatticeDeterminedByLocalLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUniqueGlobalLatticeOfLocalLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproxStabStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CoordinateLatticeUniqueTermAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalHermitianFramesTermsOrbitsLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GlobalOrbits

theorem GlobalTheory.HL.GlobalOrbits.smul_eq_of_le {F' E' : Type} [Field F'] [ValuativeRel F'] [TopologicalSpace F'] [CommRing E']
    [Algebra F' E'] [TopologicalSpace E'] (L : LocE F' E') {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E')
    (Λ : Submodule L.O (Fin n → E')) (hΛ : IsSD L Hm Λ) (u : (Fin n → E') ≃ₗ[E'] (Fin n → E'))
    (hu : u ∈ isomG L Hm) (hle : ∀ x ∈ Λ, u x ∈ Λ) : u • Λ = Λ := by sorry
