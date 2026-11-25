-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_piGal_apply
-- name    : GroundTheory.Global.SemiLocal.piGal_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:13:41.250695+00:00
-- url     : https://prove2.me/theorems/739b22f3-d408-52cd-8476-10937a99c845
-- title:
--   Semi Local: pi Gal apply
-- statement:
--   The Semi Local construction uses the pi Gal apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Galois.lean#L228-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Galois.lean#L228-L229

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

theorem GroundTheory.Global.SemiLocal.piGal_apply (σ : L ≃ₐ[K] L) (y : CompletionsOver L v) (u : PlacesOver L v) :
    piGal v σ y u = galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u) (y (σ⁻¹ • u)) := by sorry
