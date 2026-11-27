-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_galEquiv_apply
-- name    : GroundTheory.Global.SemiLocal.galEquiv_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:55:20.610146+00:00
-- url     : https://prove2.me/theorems/aadbf043-73c0-4498-93ca-f8ca3c4c4574
-- title:
--   Semi Local: gal Equiv apply
-- statement:
--   The Semi Local construction uses the gal Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Galois.lean#L186-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Galois.lean#L186-L188

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField WithZero Topology Filter TensorProduct
open scoped Pointwise
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
variable [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem GroundTheory.Global.SemiLocal.galEquiv_apply (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal] (h : w' = σ • w)
    (y : w.adicCompletion L) : galEquiv v σ w w' h y = galHom σ w w' h y := by sorry
