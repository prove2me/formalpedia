-- Prove2me | Theorems.Thm_MassDataIdxCore_key_I
-- name    : MassDataIdxCore.key_I
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:36:51.281549+00:00
-- url     : https://prove2.me/theorems/333afdf3-b3a9-4c09-b888-c65e3d394a8e
-- title:
--   Mass Data Idx Core: key I
-- statement:
--   The Mass Data Idx Core construction uses the key I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/KerBack.lean#L26-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/KerBack.lean#L26-L50

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitSmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_KerBack
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
  [DecidableEq n] {θ : T ≃ₐ[K] K × K} {s : T →+* T} (hs : ∀ t, θ (s t) = (θ t).swap) (J : Matrix n n T)
  (P : GL n K)
include hs

theorem MassDataIdxCore.key_I (g : GL n T) (hg : g ∈ Formalism.UG.UJ s J) :
    ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) * (g : Matrix n n T).map (t2 θ) =
      (conjPrime₂ θ P g⁻¹)ᵀ * ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) := by sorry
