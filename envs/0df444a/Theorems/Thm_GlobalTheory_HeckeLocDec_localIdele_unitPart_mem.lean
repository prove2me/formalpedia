-- Prove2me | Theorems.Thm_GlobalTheory_HeckeLocDec_localIdele_unitPart_mem
-- name    : GlobalTheory.HeckeLocDec.localIdele_unitPart_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:41:15.380279+00:00
-- url     : https://prove2.me/theorems/1548983a-57f3-431a-9be1-57a5baba493c
-- title:
--   Hecke Loc Dec: local Idele unit Part mem
-- statement:
--   The Hecke Loc Dec construction uses the local Idele unit Part mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeckeCharLocalValueDivUniformiserPow.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeckeCharLocalValueDivUniformiserPow.lean#L13-L28

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

theorem GlobalTheory.HeckeLocDec.localIdele_unitPart_mem (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    (x : (w.adicCompletion L)ˣ) (a : ℤ) (ha : Valued.v (x : w.adicCompletion L) = WithZero.exp (-a)) :
    localIdele L w (x * (atFin w (unif w)) ^ (-a)) ∈ PI.AlgValsFin.W.UFin L := by sorry
