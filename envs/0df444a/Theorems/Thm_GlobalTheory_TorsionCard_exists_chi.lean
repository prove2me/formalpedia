-- Prove2me | Theorems.Thm_GlobalTheory_TorsionCard_exists_chi
-- name    : GlobalTheory.TorsionCard.exists_chi
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:54:28.390835+00:00
-- url     : https://prove2.me/theorems/fa21e1b2-ecba-4649-b2ac-d7e83ed9fe53
-- title:
--   Torsion Card: exists chi
-- statement:
--   The Torsion Card construction uses the exists chi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardTorsionMulFinrank.lean#L105-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardTorsionMulFinrank.lean#L105-L113

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCosetRepresentativesOfFiniteSubgroupPadicI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ChiOntoOfUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardTorsionMulFinrank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory GlobalTheory.TorsionCard
variable {l : ℕ} [hl : Fact l.Prime]

theorem GlobalTheory.TorsionCard.exists_chi (P : LocPrime l) :
    ∃ χ : GQ l →* ℤ_[l]ˣ, ∀ g, ((χ g : ℤ_[l]) : ℚ_[l]) = (P.χQ g : ℚ_[l]) := by sorry
