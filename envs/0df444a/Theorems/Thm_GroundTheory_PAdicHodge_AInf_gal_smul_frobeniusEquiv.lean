-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_gal_smul_frobeniusEquiv
-- name    : GroundTheory.PAdicHodge.AInf.gal_smul_frobeniusEquiv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:05.388428+00:00
-- url     : https://prove2.me/theorems/a5de24ee-e4e4-47d3-a6d2-04e240158d15
-- title:
--   AInf: gal smul frobenius Equiv
-- statement:
--   The AInf construction uses the gal smul frobenius Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfGalois.lean#L158-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfGalois.lean#L158-L160

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

theorem GroundTheory.PAdicHodge.AInf.gal_smul_frobeniusEquiv (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) :
    σ • WittVector.frobeniusEquiv p _ x = WittVector.frobeniusEquiv p _ (σ • x) := by sorry
