-- Prove2me | Theorems.Thm_GlobalTheory_NL_Model_comp_tie
-- name    : GlobalTheory.NL.Model.comp_tie
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:15:28.092376+00:00
-- url     : https://prove2.me/theorems/750ecbe6-7484-4a96-86ca-452ab47074fb
-- title:
--   Model: comp tie
-- statement:
--   The Model construction uses the comp tie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L469-L479
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L469-L479

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NL GlobalTheory.NL.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

theorem GlobalTheory.NL.Model.comp_tie (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ)
    (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR)
    (hι : Comp H h i ζ τ ι) (x : ↥((H.W K s LL h).N T)) (k : ℕ) (y : TW (RA LL) T)
    (hy : TWincl (inclR LL) T y = (inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.π₁)) ^ k •
      (F.E K s LL h).tie.jD T (x : (H.W K s LL h).DD T))
    (a : ℕ) (ha : ∀ r : ℤ, r < -(a : ℤ) → (H.W K s LL h).levN T i ζ x r = 0) :
    ∃ c : ℤ, ∀ M : ℕ,
      mulVR T (tS P s ^ a) ((C.C K s LL h).tie.βdR T y) - mulVR T ((P.ιB (AI.ιA AI.π₁)) ^ k)
        (∑ r ∈ Finset.range M, mulVR T (tS P s ^ r) ((H.W K s LL h).levN T i ζ x ((r : ℤ) - (a : ℤ)))) ∈
      compKer T ι ⊔ FilV (P.PD K) (LL := ↥LL.1) (V := T.V) ((M : ℤ) - c) := by sorry
