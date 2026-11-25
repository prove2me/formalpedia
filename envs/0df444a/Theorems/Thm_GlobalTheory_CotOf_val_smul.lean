-- Prove2me | Theorems.Thm_GlobalTheory_CotOf_val_smul
-- name    : GlobalTheory.CotOf.val_smul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:25.150309+00:00
-- url     : https://prove2.me/theorems/1d6d27e8-46fa-41c5-b546-90109a9ac812
-- title:
--   Cot Of: val smul
-- statement:
--   The Cot Of construction uses the val smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvCotOfUnivDer.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvCotOfUnivDer.lean#L24-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvCotOfUnivDer
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
open GlobalTheory
open GlobalTheory.CotOf
variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}
variable (D : Dat p g B Tw Dt Oe σ cp)

theorem GlobalTheory.CotOf.val_smul {G : Type} [AddCommGroup G] (x : G) (hx : p • x = 0) (n : ℕ) :
    (n : ZMod p).val • x = n • x := by sorry
