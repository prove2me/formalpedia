-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_le_basicOpen_of_isUnit_mp
-- name    : GlobalTheory.AbCoh.le_basicOpen_of_isUnit_mp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:50:40.901666+00:00
-- url     : https://prove2.me/theorems/6110a4da-dd65-4dea-9095-0fb732f2609a
-- title:
--   Ab Coh: le basic Open of is Unit mp
-- statement:
--   The Ab Coh construction uses the le basic Open of is Unit mp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StructureSheafCohomologyBasisBijective.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StructureSheafCohomologyBasisBijective.lean#L27-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyBasisBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory GlobalTheory.AbCoh

theorem GlobalTheory.AbCoh.le_basicOpen_of_isUnit_mp {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    {T S : AffOp X} (u : T ⟶ S) (f : (OAff s).obj T) (hu : IsUnit (mp (OAff s) u f)) :
    S.unop.1 ≤ X.basicOpen (show Γ(X, T.unop.1) from f) := by sorry
