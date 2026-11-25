-- Prove2me | Theorems.Thm_GlobalTheory_TorsionCard_card_torsion
-- name    : GlobalTheory.TorsionCard.card_torsion
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:53:50.866379+00:00
-- url     : https://prove2.me/theorems/14bf731b-99e9-4b74-9d10-7c2f596486be
-- title:
--   Torsion Card: card torsion
-- statement:
--   The Torsion Card construction uses the card torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardTorsionMulFinrank.lean#L77-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardTorsionMulFinrank.lean#L77-L103

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

theorem GlobalTheory.TorsionCard.card_torsion (h2 : l ≠ 2) {Γ : Type} [Group Γ] (χ : Γ →* ℤ_[l]ˣ)
    (hχ : Function.Injective χ) (hk : ∀ x, red l x = 1 → x ∈ χ.range) :
    Nat.card {g : Γ // IsOfFinOrder g} = Nat.card ((red l).comp χ).range := by sorry
