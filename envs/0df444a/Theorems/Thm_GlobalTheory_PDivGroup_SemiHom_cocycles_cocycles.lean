-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_SemiHom_cocycles_cocycles
-- name    : GlobalTheory.PDivGroup.SemiHom.cocycles_cocycles
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:47:39.909332+00:00
-- url     : https://prove2.me/theorems/43660284-ed6a-548e-a565-bb7eb3a6461e
-- title:
--   Semi Hom: cocycles cocycles
-- statement:
--   The Semi Hom construction uses the cocycles cocycles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToBaseChangePtsBijective.lean#L385-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToBaseChangePtsBijective.lean#L385-L386

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O'']
open GlobalTheory.PDivGroup.SemiHom
variable {σ : O →+* O'} {τ : O' →+* O''} {G H : PDivGroup p O} {G' H' : PDivGroup p O'}
  {G'' : PDivGroup p O''}
variable (s : SemiHom σ G' G)
variable (t : SemiHom τ G'' G') {ρ : O →+* O''} (u : SemiHom ρ G'' G)
  (h : ∀ n a, u.app n a = t.app n (s.app n a))
include h

theorem GlobalTheory.PDivGroup.SemiHom.cocycles_cocycles (c : G.cocycles) : t.cocycles (s.cocycles c) = u.cocycles c := by sorry
