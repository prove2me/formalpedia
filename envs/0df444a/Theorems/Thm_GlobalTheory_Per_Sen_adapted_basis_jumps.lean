-- Prove2me | Theorems.Thm_GlobalTheory_Per_Sen_adapted_basis_jumps
-- name    : GlobalTheory.Per.Sen.adapted_basis_jumps
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:49:31.448456+00:00
-- url     : https://prove2.me/theorems/f68742a6-7ace-541f-9ebe-53c3368f1818
-- title:
--   Sen: adapted basis jumps
-- statement:
--   The Sen construction uses the adapted basis jumps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankSpanImageEqCard.lean#L193-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankSpanImageEqCard.lean#L193-L201

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AntitoneFiltrationExistsAdaptedLinearIndepSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankSpanImageEqCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.Per GlobalTheory.Per.Sen

theorem GlobalTheory.Per.Sen.adapted_basis_jumps : ∀ {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (D : Submodule L M) [FiniteDimensional L D] (A : ℤ → Submodule L M) (U : Multiset ℤ) (r : ℕ),
    Module.finrank L D = r → Antitone A → (∀ a, A a ≤ D) → (∀ x ∈ D, ∃ a, x ∈ A a) →
    (∀ x, (∀ a, x ∈ A a) → x = 0) →
    (∀ a : ℤ, (Module.finrank L (A a) : ℤ) - Module.finrank L (A (a + 1)) = (U.count a : ℤ)) →
    ∃ (u : Fin r → ℤ) (d : Fin r → M), Finset.univ.val.map u = U ∧ LinearIndependent L d ∧
      ∀ a, A a = Submodule.span L (d '' {k | a ≤ u k}) := by sorry
