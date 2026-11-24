-- Prove2me | Theorems.Thm_GlobalTheory_LocDualInt_exists_root_pow_cyclotomicCharacter_congr
-- name    : GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:14:36.027865+00:00
-- url     : https://prove2.me/theorems/6c5d5211-851f-43a2-88d2-840d3eaa87f5
-- title:
--   Loc Dual Int: exists root pow cyclotomic Character congr
-- statement:
--   The Loc Dual Int construction uses the exists root pow cyclotomic Character congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicCharacterCongrRootOfUnityPow.lean#L11-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicCharacterCongrRootOfUnityPow.lean#L11-L33

import Mathlib
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FactorMemCocyclesPowQuot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterCongrRootOfUnityPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
open GlobalTheory GlobalTheory.LocDualInt

theorem GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr {p : ℕ} [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (g : Formalism.GaloisCohomology.GK p K) (k : ℕ) :
    ∃ ζ : PadicAlgCl p, ζ ^ (p ^ k) = 1 ∧ ∀ a : ℕ, g ζ = ζ ^ a → (a : ZMod (p ^ k)) =
      PadicInt.toZModPow k ((cyclotomicCharacter (PadicAlgCl p) p
        (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) : ℤ_[p]ˣ) : ℤ_[p]) := by sorry
