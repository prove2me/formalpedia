-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_iwahori_inv
-- name    : GlobalTheory.CompanionTheory.TfLoc.Iw.iwahori_inv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:15:56.144541+00:00
-- url     : https://prove2.me/theorems/60e01ff5-0ca7-4e8b-8145-de5c2396f3a9
-- title:
--   Iw: iwahori inv
-- statement:
--   The Iw construction uses the iwahori inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L66-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L66-L89

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TfLoc GlobalTheory.CompanionTheory.TfLoc.Iw
variable {F : Type*} [Field F] [ValuativeRel F] {m : ℕ}

theorem GlobalTheory.CompanionTheory.TfLoc.Iw.iwahori_inv {g : GL (Fin m) F} (hg : g ∈ iwahori (m := m) F) : g⁻¹ ∈ iwahori (m := m) F := by sorry
