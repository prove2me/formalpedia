-- Prove2me | Theorems.Thm_GlobalTheory_SW_Vac_ip_smul_self
-- name    : GlobalTheory.SW.Vac.ip_smul_self
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:45:46.865484+00:00
-- url     : https://prove2.me/theorems/aa58466d-2f7e-48a9-9d97-823a495c9a91
-- title:
--   Vac: ip smul self
-- statement:
--   The Vac construction uses the ip smul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L157-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L157-L177

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.Vac.ip_smul_self (c : ℂ) (hc : c ≠ 0) (φ : Matrix κ ι ℚ → ℂ) :
    ip (c • φ) (c • φ) = c * conj c * ip φ φ := by sorry
