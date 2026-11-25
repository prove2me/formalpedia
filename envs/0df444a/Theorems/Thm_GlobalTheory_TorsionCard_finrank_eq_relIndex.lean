-- Prove2me | Theorems.Thm_GlobalTheory_TorsionCard_finrank_eq_relIndex
-- name    : GlobalTheory.TorsionCard.finrank_eq_relIndex
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:54:24.887811+00:00
-- url     : https://prove2.me/theorems/3e2b0073-b688-468c-b965-8186d2483ada
-- title:
--   Torsion Card: finrank eq rel Index
-- statement:
--   The Torsion Card construction uses the finrank eq rel Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardTorsionMulFinrank.lean#L115-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardTorsionMulFinrank.lean#L115-L128

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

theorem GlobalTheory.TorsionCard.finrank_eq_relIndex (K : FinExt l) :
    Module.finrank ↥(K0 K) ↥K.1 = (GK K).relIndex (K0 K).fixingSubgroup := by sorry
