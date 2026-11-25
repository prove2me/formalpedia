-- Prove2me | Theorems.Thm_GlobalTheory_CechCmp_cap_le
-- name    : GlobalTheory.CechCmp.cap_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:25:28.471794+00:00
-- url     : https://prove2.me/theorems/227a917b-09be-4c14-b3c3-12aee61165de
-- title:
--   Cech Cmp: cap le
-- statement:
--   The Cech Cmp construction uses the cap le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RestrictCapFBijective.lean#L53-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RestrictCapFBijective.lean#L53-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechPullOneBijectiveLatticeCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
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
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechCmp
variable {I : Type} {X : Scheme.{0}}

theorem GlobalTheory.CechCmp.cap_le (U : I → X.Opens) {S : NE I} {i : I} (h : i ∈ S.set) : cap U S ≤ U i := by sorry
