-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_Hom_txT_eq
-- name    : GlobalTheory.Ex.NumD.Hom.txT_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:08:02.779422+00:00
-- url     : https://prove2.me/theorems/a4cb01d9-b424-4dcd-a8ef-242d1178a62c
-- title:
--   Hom: tx T eq
-- statement:
--   The Hom construction uses the tx T eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean#L188-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean#L188-L202

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD GlobalTheory.Ex.NumD.Hom
variable {O O' : Type} [CommRing O] [CommRing O'] {f : O →+* O'} {N : NumD O} {N' : NumD O'} (I : NumD.Hom f N N')
local notation "F" => Units.map (RingHom.toMonoidHom f)

theorem GlobalTheory.Ex.NumD.Hom.txT_eq {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (p' : N'.QT (m ^ 2)) (ep : p'.1.1.toAdd = I.e p.1.1.toAdd)
    (hp : I.Rel p.1.2 p'.1.2) (χ : N.X) : N'.txT m p' (I.e χ) = I.lam * f (N.txT m p χ) := by sorry
