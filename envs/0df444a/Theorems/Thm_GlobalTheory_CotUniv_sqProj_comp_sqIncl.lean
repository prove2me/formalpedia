-- Prove2me | Theorems.Thm_GlobalTheory_CotUniv_sqProj_comp_sqIncl
-- name    : GlobalTheory.CotUniv.sqProj_comp_sqIncl
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:27:11.579806+00:00
-- url     : https://prove2.me/theorems/3d6d9a10-ed8a-45fa-8842-99fcb3b44b65
-- title:
--   Cot Univ: sq Proj comp sq Incl
-- statement:
--   The Cot Univ construction uses the sq Proj comp sq Incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L122-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L122-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FstHomCompSqzOfLeibniz
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_UniversalDerivation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory GlobalTheory.CotUniv
variable {R₀ : Type} [CommRing R₀] (O : LAlg R₀)
  (M : Type) [AddCommGroup M] [Module (O : Type) M]
variable {O M}
variable (O M)

theorem GlobalTheory.CotUniv.sqProj_comp_sqIncl : (sqProj O M).comp (sqIncl O M) = LHom.id O := by sorry
