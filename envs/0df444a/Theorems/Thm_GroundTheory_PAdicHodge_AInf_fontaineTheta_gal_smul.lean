-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_fontaineTheta_gal_smul
-- name    : GroundTheory.PAdicHodge.AInf.fontaineTheta_gal_smul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:39:25.142234+00:00
-- url     : https://prove2.me/theorems/342eae2b-aa8e-487d-8346-2200d2e66040
-- title:
--   AInf: fontaine Theta gal smul
-- statement:
--   The AInf construction uses the fontaine Theta gal smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfGalois.lean#L152-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfGalois.lean#L152-L156

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

theorem GroundTheory.PAdicHodge.AInf.fontaineTheta_gal_smul (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) :
    ((WittVector.fontaineTheta (normInteger ℂ_[p]) p (σ • x) : normInteger ℂ_[p]) : ℂ_[p]) =
      σ • ((WittVector.fontaineTheta (normInteger ℂ_[p]) p x : normInteger ℂ_[p]) : ℂ_[p]) := by sorry
