-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_valuation_eq_exp
-- name    : GroundTheory.Global.exists_valuation_eq_exp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:50:23.055022+00:00
-- url     : https://prove2.me/theorems/98a351fd-9697-4b8d-8f77-c9d5964d2e61
-- title:
--   Global: exists valuation eq exp
-- statement:
--   The Global construction uses the exists valuation eq exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean#L140-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean#L140-L176

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminantLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.LocalField
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {M : Type*} [Field M] [NumberField M]

theorem GroundTheory.Global.exists_valuation_eq_exp (w : HeightOneSpectrum (𝓞 M)) (n : ℕ) :
    ∃ x : M, w.valuation M x = WithZero.exp (n : ℤ) ∧
      ∀ u : HeightOneSpectrum (𝓞 M), u ≠ w → u.valuation M x ≤ 1 := by sorry
