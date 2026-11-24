-- Prove2me | Theorems.Thm_GlobalTheory_CotUniv_tg_act
-- name    : GlobalTheory.CotUniv.tg_act
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:27:39.960896+00:00
-- url     : https://prove2.me/theorems/73f7066d-6461-44bf-b0be-a174113f8b94
-- title:
--   Cot Univ: tg act
-- statement:
--   The Cot Univ construction uses the tg act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L272-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L272-L290

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

theorem GlobalTheory.CotUniv.tg_act {E : Type} [CommRing E] (Ac : OAct B O p E) (a : E) (gb : Module.Basis (Fin g) R₀ B.gg)
    (m : Fin g → M) (hm : ∀ k, p • m k = 0) (x : torP B p (sqAlg O M))
    (hx : (x : B.G (sqAlg O M)) = tgPt B O gb m) :
    (Ac.act a (sqAlg O M) (sqIncl O M) x : B.G (sqAlg O M)) =
      tgPt B O gb fun k' => ∑ k, algebraMap R₀ (O : Type) (gb.repr (Ac.actL a (gb k)) k') • m k := by sorry
