-- Prove2me | Theorems.Thm_GlobalTheory_DI_divided_frob_logForm
-- name    : GlobalTheory.DI.divided_frob_logForm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:03:22.981168+00:00
-- url     : https://prove2.me/theorems/e1b0a7cf-c2a2-52dd-ae12-04116bc3944f
-- title:
--   DI: divided frob log Form
-- statement:
--   The DI construction uses the divided frob log Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DividedFrobLogForm.lean#L10-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DividedFrobLogForm.lean#L10-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DividedFrobLogForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI

theorem GlobalTheory.DI.divided_frob_logForm : ∀ {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p] (π : Kt →+* K) {ι : Type} (F : ι → Kt →+* Kt) (f : ι → Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) (h : ι → ι → Ω[K⁄ℤ] →+ K) (s : Finset ι) (A : Subring K) (g : K), (∀ i, IsF p π (F i) (f i)) → (∀ i j, IsH p π (F i) (F j) (h i j)) → LogLift p π F s (A : Set K) g → (∀ i ∈ s, ∃ w ∈ A, g ≠ 0 → f i (g⁻¹ • KaehlerDifferential.D ℤ K g) = g⁻¹ • KaehlerDifferential.D ℤ K g + KaehlerDifferential.D ℤ K w) ∧ ∀ i ∈ s, ∀ j ∈ s, h i j (g⁻¹ • KaehlerDifferential.D ℤ K g) ∈ A := by sorry
