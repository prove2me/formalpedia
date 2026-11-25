-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tate_natTrans_eq_of_eq_zero
-- name    : GroundTheory.GroupCoh.tate_natTrans_eq_of_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:15:52.918304+00:00
-- url     : https://prove2.me/theorems/af1b2fa7-9314-4dcf-a091-5f7ba9412afb
-- title:
--   Group Coh: tate nat Trans eq of eq zero
-- statement:
--   The Group Coh construction uses the tate nat Trans eq of eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateUnique.lean#L16-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateUnique.lean#L16-L50

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
omit [Fintype G]

theorem GroundTheory.GroupCoh.tate_natTrans_eq_of_eq_zero {U V : Type u} [Group U] [Group V] [Fintype U] [Fintype V]
    (E : Rep.{u} k G ⥤ Rep.{u} k U) (E' : Rep.{u} k G ⥤ Rep.{u} k V)
    [E.PreservesZeroMorphisms] [E'.PreservesZeroMorphisms]
    (hE : ∀ {X : ShortComplex (Rep.{u} k G)}, X.ShortExact → (X.map E).ShortExact)
    (hE' : ∀ {X : ShortComplex (Rep.{u} k G)}, X.ShortExact → (X.map E').ShortExact)
    (hEc : ∀ A : Rep.{u} k G, TateAcyclic (E.obj (coindSES.obj A).X₂))
    (hEi : ∀ A : Rep.{u} k G, TateAcyclic (E'.obj (indSES.obj A).X₂))
    (α β : ∀ n : ℤ, E ⋙ tateCohomologyFunctor n ⟶ E' ⋙ tateCohomologyFunctor n)
    (hα : ∀ {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ),
      TateCohomology.δ (hE hX) n ≫ (α (n + 1)).app X.X₁ =
        (α n).app X.X₃ ≫ TateCohomology.δ (hE' hX) n)
    (hβ : ∀ {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ),
      TateCohomology.δ (hE hX) n ≫ (β (n + 1)).app X.X₁ =
        (β n).app X.X₃ ≫ TateCohomology.δ (hE' hX) n)
    (h0 : α 0 = β 0) (n : ℤ) : α n = β n := by sorry
