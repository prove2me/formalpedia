-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_fam_of_isPullDeg_alt
-- name    : GlobalTheory.T.exists_fam_of_isPullDeg_alt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:36:18.57813+00:00
-- url     : https://prove2.me/theorems/433c5323-0ea0-4758-9441-d2058a04d05d
-- title:
--   T: exists fam of is Pull Deg alt
-- statement:
--   The T construction uses the exists fam of is Pull Deg alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFamOfIsPullDegStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFamOfIsPullDegStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDegStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.T.exists_fam_of_isPullDeg_alt : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (k : ℕ) (F : Fam D (FractionRing R) k) (f : ∀ α, D.SecB k α) (f' : ∀ α, D'.SecB k α), (∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (F.s α) (D.famφB α) (DegPre.famε k) (f α) (DegPre.prB D (FractionRing R)).left 1) → (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.P.L.U (p κ)) → (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) z (LB.wchart D.P.L (D.famφB (hD.xe x)) p) ((f (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' x).f q))) → ∃ F' : Fam D' (FractionRing R') k, (∀ α, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) (F'.s α) (D'.famφB α) (DegPre.famε k) (f' α) (DegPre.prB D' (FractionRing R')).left 1) := by sorry
