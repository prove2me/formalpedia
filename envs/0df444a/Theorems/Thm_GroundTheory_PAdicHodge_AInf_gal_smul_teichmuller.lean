-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_gal_smul_teichmuller
-- name    : GroundTheory.PAdicHodge.AInf.gal_smul_teichmuller
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:17.77981+00:00
-- url     : https://prove2.me/theorems/4b94f35c-028a-4d71-ba8b-096b8dbeadc1
-- title:
--   AInf: gal smul teichmuller
-- statement:
--   The AInf construction uses the gal smul teichmuller property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfGalois.lean#L141-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfGalois.lean#L141-L144

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

theorem GroundTheory.PAdicHodge.AInf.gal_smul_teichmuller (σ : Gal(PadicAlgCl p/K)) (x : PreTilt (normInteger ℂ_[p]) p) :
    σ • (WittVector.teichmuller p x : AInf ℂ_[p] p) =
      WittVector.teichmuller p (preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (norm_galCp_toRingHom σ) x) := by sorry
