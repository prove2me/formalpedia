-- Prove2me | Theorems.Thm_MassDataIdxCore_psi_map
-- name    : MassDataIdxCore.psi_map
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:11:35.842269+00:00
-- url     : https://prove2.me/theorems/7e4e8b5c-9536-4785-9287-8cdc9757f479
-- title:
--   Mass Data Idx Core: psi map
-- statement:
--   The Mass Data Idx Core construction uses the psi map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/PsiKerIff.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/PsiKerIff.lean#L57-L59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitTensorVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_PsiKerIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n]
variable (θ : T ≃ₐ[K] K × K) (J : Matrix n n T) (P : GL n K) {H : Type} [Group H] (m : H →* GL n T)
  (hK : ∀ h x, x ∈ Lat O θ J P ↔ ((m h : GL n T) : Matrix n n T) *ᵥ x ∈ Lat O θ J P)

theorem MassDataIdxCore.psi_map (h : H) : ((psi O θ J P m hK h : GL n O) : Matrix n n O).map (algebraMap O K) =
    conjPrime₂ θ P (m h) := by sorry
