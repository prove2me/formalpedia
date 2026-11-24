-- Prove2me | Theorems.Thm_GlobalTheory_KS_Kunneth_functional_cob
-- name    : GlobalTheory.KS.Kunneth.functional_cob
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:45:44.0657+00:00
-- url     : https://prove2.me/theorems/1b586b85-aa9b-4c01-b0cb-19eee63e35d4
-- title:
--   Kunneth: functional cob
-- statement:
--   The Kunneth construction uses the functional cob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KunnethSymmProductAffineCovers.lean#L155-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KunnethSymmProductAffineCovers.lean#L155-L185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDualFamilyModSubspace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCovers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Kunneth

theorem GlobalTheory.KS.Kunneth.functional_cob {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} [Fintype I] [DecidableEq I]
    {U : I → Y.Opens} (α : C1 U →+ K) (h : ∀ c, IsCob U c → α c = 0) (j : I) (b : Γ(Y, U j)) :
    ∑ k, α (Pi.single k (Pi.single j (rsT b (U k ⊓ U j)))) =
      ∑ k, α (Pi.single j (Pi.single k (rsT b (U j ⊓ U k)))) := by sorry
