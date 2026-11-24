-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_CombEx_comp_combHom
-- name    : GlobalTheory.SecGlue.CombEx.comp_combHom
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:49:42.378176+00:00
-- url     : https://prove2.me/theorems/1af766c4-4809-4637-a594-9ac25aa0e75a
-- title:
--   Comb Ex: comp comb Hom
-- statement:
--   The Comb Ex construction uses the comp comb Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineCombinationSquareZeroLiftsChart.lean#L94-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineCombinationSquareZeroLiftsChart.lean#L94-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.CombEx

theorem GlobalTheory.SecGlue.CombEx.comp_combHom {A S T : Type} [CommRing A] [CommRing S] [CommRing T] (q : S →+* T)
    (hsq : RingHom.ker q ^ 2 = ⊥) {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S)
    (hq : ∀ i, q.comp (ψ i) = q.comp φ) : q.comp (combHom q hsq φ ψ a hq) = q.comp φ := by sorry
