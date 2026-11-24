-- Prove2me | Theorems.Thm_GlobalTheory_CotUniv_sqProj_comp_sqMap
-- name    : GlobalTheory.CotUniv.sqProj_comp_sqMap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:27:23.638007+00:00
-- url     : https://prove2.me/theorems/b8f00055-9ddf-44df-baac-99b875790219
-- title:
--   Cot Univ: sq Proj comp sq Map
-- statement:
--   The Cot Univ construction uses the sq Proj comp sq Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L268-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L268-L270

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
variable {R₀ : Type} [CommRing R₀] {B : BX R₀} {O A : LAlg R₀} {p g : ℕ}
  {sO : LHom O A} {ε : LHom A O} {y : B.G A} {w : Fin g → B.gg}
variable {M : Type} [AddCommGroup M] [Module (O : Type) M]
variable {M' : Type} [AddCommGroup M'] [Module (O : Type) M']

theorem GlobalTheory.CotUniv.sqProj_comp_sqMap (φ : LHom A (sqAlg O M)) (h2 : (sqProj O M).comp φ = ε)
    (u : M →ₗ[(O : Type)] M') : (sqProj O M').comp ((sqMap u).comp φ) = ε := by sorry
