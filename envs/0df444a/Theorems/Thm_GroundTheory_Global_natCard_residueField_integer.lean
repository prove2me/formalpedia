-- Prove2me | Theorems.Thm_GroundTheory_Global_natCard_residueField_integer
-- name    : GroundTheory.Global.natCard_residueField_integer
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:24:36.937969+00:00
-- url     : https://prove2.me/theorems/b6b29b0f-b4f1-4156-a41d-61473b53f344
-- title:
--   Global: nat Card residue Field integer
-- statement:
--   The Global construction uses the nat Card residue Field integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Inertia.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Inertia.lean#L28-L30

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Inertia
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField
open scoped WithZero Pointwise
open GroundTheory GroundTheory.Global
variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem GroundTheory.Global.natCard_residueField_integer :
    Nat.card 𝓀[u.adicCompletion F] = Nat.card (𝓞 F ⧸ u.asIdeal) := by sorry
