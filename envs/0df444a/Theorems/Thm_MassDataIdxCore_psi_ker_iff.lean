-- Prove2me | Theorems.Thm_MassDataIdxCore_psi_ker_iff
-- name    : MassDataIdxCore.psi_ker_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:11:30.855838+00:00
-- url     : https://prove2.me/theorems/f324c7df-d5d2-4490-93e2-bca30a6809a8
-- title:
--   Mass Data Idx Core: psi ker iff
-- statement:
--   The Mass Data Idx Core construction uses the psi ker iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/PsiKerIff.lean#L61-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/PsiKerIff.lean#L61-L84

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

theorem MassDataIdxCore.psi_ker_iff (c : O) (h : H) :
    (∀ i j, (((psi O θ J P m hK h : GL n O) : Matrix n n O) - 1) i j ∈ Ideal.span {c}) ↔
      ∀ i j, ∃ w ∈ O, (conjPrime₂ θ P (m h) - 1) i j = (c : K) * w := by sorry
