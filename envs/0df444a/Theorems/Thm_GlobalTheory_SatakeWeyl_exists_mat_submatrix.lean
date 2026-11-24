-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_exists_mat_submatrix
-- name    : GlobalTheory.SatakeWeyl.exists_mat_submatrix
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:46:53.02763+00:00
-- url     : https://prove2.me/theorems/d05afa42-9b64-4c25-843c-fd4bba4500ff
-- title:
--   Satake Weyl: exists mat submatrix
-- statement:
--   The Satake Weyl construction uses the exists mat submatrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryUnipotentRadicalSplittingOfLeviPart.lean#L15-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryUnipotentRadicalSplittingOfLeviPart.lean#L15-L33

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryUnipotentRadicalSplittingOfLeviPart
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl

theorem GlobalTheory.SatakeWeyl.exists_mat_submatrix {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n r : ℕ}
    (e : Fin r → Fin n) (he : Function.Injective e) (hrev : ∀ i, e i.rev = (e i).rev) (m : GU σ n)
    (hm : ∀ a b, (a ∉ Set.range e ∨ b ∉ Set.range e) → mat m a b = (1 : Matrix (Fin n) (Fin n) L) a b) :
    ∃ a : GU σ r, mat a = (mat m).submatrix e e := by sorry
