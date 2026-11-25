-- Prove2me | Theorems.Thm_GlobalTheory_Per_weierstrass_test
-- name    : GlobalTheory.Per.weierstrass_test
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:49:57.476602+00:00
-- url     : https://prove2.me/theorems/5f1ad08f-8d47-5cf9-bba5-331feb8c78ba
-- title:
--   Per: weierstrass test
-- statement:
--   The Per construction uses the weierstrass test property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ProdPrimePowDvd.lean#L121-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ProdPrimePowDvd.lean#L121-L145

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ProdPrimePowDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory GlobalTheory.Per

theorem GlobalTheory.Per.weierstrass_test : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O], ∀ (LL : Type) [Field LL] [Algebra O LL] [IsFractionRing O LL] (ι : Type) [Fintype ι] (x : ι → O) (m : ι → ℕ), Function.Injective x → (∀ k, ¬ IsUnit (x k)) → ∀ (ev : ι → (PowerSeries O →ₐ[O] PowerSeries LL)), (∀ k, ∃ w : PowerSeries LL, IsUnit w ∧ ev k PowerSeries.X = PowerSeries.C (algebraMap O LL (x k)) + PowerSeries.X * w) → ∀ a : PowerSeries O, (∀ k, PowerSeries.X ^ m k ∣ ev k a) ↔ (∏ k, (PowerSeries.X - PowerSeries.C (x k)) ^ m k) ∣ a := by sorry
