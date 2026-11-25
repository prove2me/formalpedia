-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_tri_res_resO
-- name    : GlobalTheory.CechDR.tri_res_resO
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:50:41.380279+00:00
-- url     : https://prove2.me/theorems/b28806f9-bcbd-4729-aea7-d5a181595f38
-- title:
--   Cech DR: tri res res O
-- statement:
--   The Cech DR construction uses the tri res res O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StructureSheafCohomologyPullbackCompCupId.lean#L136-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StructureSheafCohomologyPullbackCompCupId.lean#L136-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupId
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CechDR
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {ψ : X'' ⟶ X'} {φ : X' ⟶ X}
variable (ψ φ)

theorem GlobalTheory.CechDR.tri_res_resO (s'' : X'' ⟶ Sp R'') :
    (∀ a : HO1 s'', (cechTripleRestrictFirst ψ φ s'').pull1 ((pairRes ψ s'').pull1 a) =
      (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 a)) ∧
    (∀ a : HO2 s'', (cechTripleRestrictFirst ψ φ s'').pull2 ((pairRes ψ s'').pull2 a) =
      (cechTripleRestrictComposite ψ φ s'').pull2 ((pairRes (ψ ≫ φ) s'').pull2 a)) ∧
    (∀ a : GlobForm s'', pullGlob1 (cechTripleRestrictFirst ψ φ s'') (pullGlob1 (pairRes ψ s'') a) =
      pullGlob1 (cechTripleRestrictComposite ψ φ s'') (pullGlob1 (pairRes (ψ ≫ φ) s'') a)) := by sorry
