-- Prove2me | Theorems.Thm_GlobalTheory_HeckeLocDec_loc_div_val_pow
-- name    : GlobalTheory.HeckeLocDec.loc_div_val_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:41:20.879083+00:00
-- url     : https://prove2.me/theorems/71e69361-9dfd-4a1b-9e11-bc6f5c08f6ea
-- title:
--   Hecke Loc Dec: loc div val pow
-- statement:
--   The Hecke Loc Dec construction uses the loc div val pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeckeCharLocalValueDivUniformiserPow.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeckeCharLocalValueDivUniformiserPow.lean#L30-L44

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeckeCharLocalValueDivUniformiserPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Host
noncomputable section
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory GlobalTheory.HeckeLocDec

theorem GlobalTheory.HeckeLocDec.loc_div_val_pow (L : Type) [Field L] [NumberField L] (χ : HChar L) :
    ∃ N : ℕ, 0 < N ∧ ∀ (w : HeightOneSpectrum (𝓞 L)) (x : (w.adicCompletion L)ˣ),
      ∃ a : ℤ, ((χ.loc w x / χ.val w ^ a : ℂˣ) : ℂ) ^ N = 1 := by sorry
