-- Prove2me | Theorems.Thm_GlobalTheory_CotUniv_sqMap_comp_sO
-- name    : GlobalTheory.CotUniv.sqMap_comp_sO
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:27:18.4806+00:00
-- url     : https://prove2.me/theorems/7b8801dd-aae0-46ee-a86c-8251c7be2a9e
-- title:
--   Cot Univ: sq Map comp s O
-- statement:
--   The Cot Univ construction uses the sq Map comp s O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L260-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L260-L266

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

theorem GlobalTheory.CotUniv.sqMap_comp_sO (φ : LHom A (sqAlg O M)) (h1 : φ.comp sO = sqIncl O M)
    (u : M →ₗ[(O : Type)] M') : ((sqMap u).comp φ).comp sO = sqIncl O M' := by sorry
