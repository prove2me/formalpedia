-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_coe_untilt_gal
-- name    : GroundTheory.PAdicHodge.AInf.coe_untilt_gal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:00.833339+00:00
-- url     : https://prove2.me/theorems/9310c5bf-09eb-497b-9798-84eb190f7fa8
-- title:
--   AInf: coe untilt gal
-- statement:
--   The AInf construction uses the coe untilt gal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfGalois.lean#L146-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfGalois.lean#L146-L150

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem GroundTheory.PAdicHodge.AInf.coe_untilt_gal (σ : Gal(PadicAlgCl p/K)) (x : PreTilt (normInteger ℂ_[p]) p) :
    ((PreTilt.untilt (preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (norm_galCp_toRingHom σ) x) :
      normInteger ℂ_[p]) : ℂ_[p]) = σ • ((PreTilt.untilt x : normInteger ℂ_[p]) : ℂ_[p]) := by sorry
