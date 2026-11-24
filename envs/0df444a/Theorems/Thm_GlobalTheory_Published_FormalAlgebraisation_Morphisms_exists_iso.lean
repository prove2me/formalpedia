-- Prove2me | Theorems.Thm_GlobalTheory_Published_FormalAlgebraisation_Morphisms_exists_iso
-- name    : GlobalTheory.Published.FormalAlgebraisation.Morphisms.exists_iso
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:56:54.431253+00:00
-- url     : https://prove2.me/theorems/919131c9-817c-4850-b575-4e1f2298f54a
-- title:
--   Morphisms: exists iso
-- statement:
--   The Morphisms construction uses the exists iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/FormalAlgebraisation.lean#L73-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/FormalAlgebraisation.lean#L73-L93

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.FormalAlgebraisation
variable {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R}

theorem GlobalTheory.Published.FormalAlgebraisation.Morphisms.exists_iso (H : Morphisms) (hI : IsAdicComplete I R)
    {X X' : Over (Spec (CommRingCat.of R))} [hX : IsProper X.hom] [hX' : IsProper X'.hom]
    {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {b : ∀ e, (Y e).left ⟶ X.left}
    {b' : ∀ e, (Y e).left ⟶ X'.left}
    (hb : ∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) (hβ : ∀ e, β e ≫ b (e + 1) = b e)
    (hb' : ∀ e, IsPullback (b' e) (Y e).hom X'.hom (thick R I e))
    (hβ' : ∀ e, β e ≫ b' (e + 1) = b' e) :
    ∃ g : X ≅ X', (∀ e, b e ≫ g.hom.left = b' e) ∧
      ∀ g' : X ⟶ X', (∀ e, b e ≫ g'.left = b' e) → g' = g.hom := by sorry
