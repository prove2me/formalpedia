-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Vf2_exists_decomp
-- name    : GlobalTheory.ThK.Dbl.Vf2.exists_decomp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:41:21.508884+00:00
-- url     : https://prove2.me/theorems/fe35d354-997a-54a5-988d-4e5722f22c5b
-- title:
--   Vf2: exists decomp
-- statement:
--   The Vf2 construction uses the exists decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/SkewTwo.lean#L165-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/SkewTwo.lean#L165-L236

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_SkewTwo
import Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_exists_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Vf2
open Matrix GlobalTheory.WeilM PositivityTheory.ThKG.Loc.Cone.Vf
variable {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] {c : A →ₐ[R] A} [Fintype β] [DecidableEq β] {J : Matrix β β A}

theorem GlobalTheory.ThK.Dbl.Vf2.exists_decomp {b b' x y t' : Matrix β β A} (b1 : Adj c J b b') (hb : b + b' = -1) (g : UG c (dbl J))
    (hg : g.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = fromRows x y) (ht : (y + b * (y - x)) * t' = 1) {ε : A} (he : ε * ε = ε)
    (hc : c ε = ε) (hm : ε • (y - x) = y - x) :
    ∃ (s n p : UG c (dbl J)) (t : GL β A), s * s = 1 ∧ g = s * n * s * p ∧ s.1.1 = CC b * SS ε * Ci b ∧
      n.1.1 = CC b * fromBlocks 1 (-((y - x) * t')) 0 1 * Ci b ∧ (n⁻¹).1.1 = CC b * fromBlocks 1 ((y - x) * t') 0 1 * Ci b ∧
      n.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * (1 : GL β A).1 ∧
      p.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * t.1 ∧
      t.1 = y + b * (y - x) ∧ (t⁻¹).1 = t' := by sorry
