-- Prove2me | Theorems.Thm_GlobalTheory_TorsionCard_card_torsion_mul_finrank
-- name    : GlobalTheory.TorsionCard.card_torsion_mul_finrank
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:10:25.218106+00:00
-- url     : https://prove2.me/theorems/e1e6415c-43b7-58a2-adf6-d0a21b1b6d29
-- title:
--   Torsion Card: card torsion mul finrank
-- statement:
--   The Torsion Card construction uses the card torsion mul finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardTorsionMulFinrank.lean#L132-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardTorsionMulFinrank.lean#L132-L244

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
set_option maxHeartbeats 800000

theorem GlobalTheory.TorsionCard.card_torsion_mul_finrank : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ} (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n), l ≠ 2 → K.1 ≤ Ks K 1 → W.DelF.card * Module.finrank ↥(K0 K) ↥K.1 = l - 1 := by sorry
