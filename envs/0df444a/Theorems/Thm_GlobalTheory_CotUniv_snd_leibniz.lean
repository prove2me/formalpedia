-- Prove2me | Theorems.Thm_GlobalTheory_CotUniv_snd_leibniz
-- name    : GlobalTheory.CotUniv.snd_leibniz
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:27:28.750427+00:00
-- url     : https://prove2.me/theorems/69dd08a8-6197-41cd-9a7e-bd3cbe5b6565
-- title:
--   Cot Univ: snd leibniz
-- statement:
--   The Cot Univ construction uses the snd leibniz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L235-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L235-L240

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

theorem GlobalTheory.CotUniv.snd_leibniz (φ : LHom A (sqAlg O M)) (h2 : (sqProj O M).comp φ = ε) (f f' : (A : Type)) :
    SqExt.snd (O := (O : Type)) (M := M) (φ.1 (f * f')) =
      ε.1 f • SqExt.snd (O := (O : Type)) (M := M) (φ.1 f') +
        ε.1 f' • SqExt.snd (O := (O : Type)) (M := M) (φ.1 f) := by sorry
