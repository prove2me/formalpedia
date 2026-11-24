-- Prove2me | Theorems.Thm_GlobalTheory_CotUniv_snd_smul
-- name    : GlobalTheory.CotUniv.snd_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:27:15.718016+00:00
-- url     : https://prove2.me/theorems/7a2285c9-e5e6-4136-bcd7-b0ddca8c8226
-- title:
--   Cot Univ: snd smul
-- statement:
--   The Cot Univ construction uses the snd smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L226-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L226-L233

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

theorem GlobalTheory.CotUniv.snd_smul (φ : LHom A (sqAlg O M)) (h1 : φ.comp sO = sqIncl O M) (o : (O : Type))
    (f : (A : Type)) :
    SqExt.snd (O := (O : Type)) (M := M) (φ.1 (sO.1 o * f)) =
      o • SqExt.snd (O := (O : Type)) (M := M) (φ.1 f) := by sorry
