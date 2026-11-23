-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_Approx_abv_pairwise
-- name    : GlobalTheory.LocalQuad.Approx.abv_pairwise
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:39.835941+00:00
-- url     : https://prove2.me/theorems/88dc6145-b6bd-4e6d-be47-0f6bfd8737ec
-- title:
--   Approx: abv pairwise
-- statement:
--   The Approx construction uses the abv pairwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsForallAbvSubLt.lean#L70-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsForallAbvSubLt.lean#L70-L98

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

theorem GlobalTheory.LocalQuad.Approx.abv_pairwise (T : Finset (HeightOneSpectrum (𝓞 F))) :
    Pairwise fun i j ↦ ¬(_root_.GlobalTheory.LocalQuad.Approx.abv T i).IsEquiv
      (_root_.GlobalTheory.LocalQuad.Approx.abv T j) := by sorry
