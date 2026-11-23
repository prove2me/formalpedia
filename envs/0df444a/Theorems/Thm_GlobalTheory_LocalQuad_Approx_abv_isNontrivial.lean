-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_Approx_abv_isNontrivial
-- name    : GlobalTheory.LocalQuad.Approx.abv_isNontrivial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:34.362335+00:00
-- url     : https://prove2.me/theorems/14d82809-bd5e-4508-b5a8-5cafafeb58b6
-- title:
--   Approx: abv is Nontrivial
-- statement:
--   The Approx construction uses the abv is Nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsForallAbvSubLt.lean#L42-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsForallAbvSubLt.lean#L42-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsForallAbvSubLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad GlobalTheory.LocalQuad.Approx
variable {F : Type} [Field F] [NumberField F]
open NumberField IsDedekindDomain
open scoped Matrix WithZero
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.LocalQuad.Approx.abv_isNontrivial (T : Finset (HeightOneSpectrum (𝓞 F)))
    (i : T ⊕ (F →+* ℝ)) : (_root_.GlobalTheory.LocalQuad.Approx.abv T i).IsNontrivial := by sorry
