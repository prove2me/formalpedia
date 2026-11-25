-- Prove2me | Theorems.Thm_GlobalTheory_ResidueCharacterDense_resChar_eq_iff
-- name    : GlobalTheory.ResidueCharacterDense.resChar_eq_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:26:30.556964+00:00
-- url     : https://prove2.me/theorems/0df788ce-2683-46fe-b148-adcfcdf8a951
-- title:
--   Residue Character Dense: res Char eq iff
-- statement:
--   The Residue Character Dense construction uses the res Char eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L115-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L115-L120

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense

theorem GlobalTheory.ResidueCharacterDense.resChar_eq_iff {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (hp : (Formalism.MainNotions.S.Loc.resChar p).Prime) {l : ℕ} (hl : l.Prime) :
    Formalism.MainNotions.S.Loc.resChar p = l ↔ (l : 𝓞 F) ∈ p.asIdeal := by sorry
