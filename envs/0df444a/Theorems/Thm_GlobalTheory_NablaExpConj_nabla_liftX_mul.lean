-- Prove2me | Theorems.Thm_GlobalTheory_NablaExpConj_nabla_liftX_mul
-- name    : GlobalTheory.NablaExpConj.nabla_liftX_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:58.870735+00:00
-- url     : https://prove2.me/theorems/70bcd3e4-6908-4e7c-b1c4-7b0e2d53161a
-- title:
--   Nabla Exp Conj: nabla lift X mul
-- statement:
--   The Nabla Exp Conj construction uses the nabla lift X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExpSNegMulExpS.lean#L68-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExpSNegMulExpS.lean#L68-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.NablaExpConj
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
omit [Algebra ℚ k]

theorem GlobalTheory.NablaExpConj.nabla_liftX_mul (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u φ : Fin d → k) (f : PS k 1 d)
    (G : AA k d) :
    nabla k B h m u φ (liftX k f * G) =
      liftX k f * nabla k B h m u φ G + liftX k (Dof (B.FK k) u f) * G := by sorry
