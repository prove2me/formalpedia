-- Prove2me | Theorems.Thm_MassDataIdxFrA_clause_iff
-- name    : MassDataIdxFrA.clause_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:51:59.445622+00:00
-- url     : https://prove2.me/theorems/5632a57f-569d-48aa-ba25-734a317ddd90
-- title:
--   Mass Data Idx Fr A: clause iff
-- statement:
--   The Mass Data Idx Fr A construction uses the clause iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/Imports.lean#L12-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/Imports.lean#L12-L127

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_CongSpanSingleIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxFrA
open Matrix
variable {F k : Type} [Field F] [Field k] (O : ValuationSubring F) (π : O →+* k) (γ : O)
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem MassDataIdxFrA.clause_iff (hker : RingHom.ker π = Ideal.span {γ}) (Y : Matrix ι ι O) {β : Type} (u : β → ι → F)
    (pos : β → ι) (hu : ∀ b, ∃ z, IntVec O z ∧ u b = Pi.single (pos b) 1 + (γ : F) • z) (s : Set β)
    (w : ι → F) (j : ι) (hw : ∃ z, IntVec O z ∧ w = Pi.single j 1 + (γ : F) • z) :
    CongSpan O γ (u '' s) ((Y.map ((↑) : O → F) - 1) *ᵥ w) ↔
      ∀ i, i ∉ pos '' s → π (Y i j) = if i = j then 1 else 0 := by sorry
