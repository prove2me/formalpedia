-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisExt_ext_mul
-- name    : GlobalTheory.CompanionTheory.RgEisExt.ext_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:58:21.652248+00:00
-- url     : https://prove2.me/theorems/65755c92-9a80-4833-b728-930fb6440af4
-- title:
--   Rg Eis Ext: ext mul
-- statement:
--   The Rg Eis Ext construction uses the ext mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExtensionLaw.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExtensionLaw.lean#L13-L27

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SectionLawHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExtensionLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisExt
variable {G : Type} [Group G]

theorem GlobalTheory.CompanionTheory.RgEisExt.ext_mul {K P : Subgroup G} {f : G → ℝ} (hadd : ∀ p ∈ P, ∀ q ∈ P, f (p * q) = f p + f q)
    (hfK : ∀ p ∈ P, p ∈ K → f p = 0) {p k : G} (hp : p ∈ P) (hk : k ∈ K) :
    PositivityTheory.RgEis.ext K P f (p * k) = f p := by sorry
