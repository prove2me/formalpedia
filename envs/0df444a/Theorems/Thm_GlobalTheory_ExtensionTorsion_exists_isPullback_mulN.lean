-- Prove2me | Theorems.Thm_GlobalTheory_ExtensionTorsion_exists_isPullback_mulN
-- name    : GlobalTheory.ExtensionTorsion.exists_isPullback_mulN
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:19:08.406213+00:00
-- url     : https://prove2.me/theorems/a65f88c1-2dc6-485c-a8f1-3fb0cfd08ab5
-- title:
--   Extension Torsion: exists is Pullback mul N
-- statement:
--   The Extension Torsion construction uses the exists is Pullback mul N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsFiniteFlatTorsionOfIsGt.lean#L30-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsFiniteFlatTorsionOfIsGt.lean#L30-L70

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsFiniteFlatTorsionOfIsGt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.ExtensionTorsion
open KernelNoTorsion
variable {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]

theorem GlobalTheory.ExtensionTorsion.exists_isPullback_mulN [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ)
    {P Q : Over S} {a : P ⟶ G} {b : P ⟶ torsion B N} (hP : IsPullback a b q (torsion.ι B N))
    {s : Q ⟶ P} {r : Q ⟶ torsion G N} (hQ : IsPullback s r b (torsionHom q N)) :
    ∃ (c : P ⟶ T) (t : Q ⟶ T), IsPullback s t c (mulN T N) := by sorry
