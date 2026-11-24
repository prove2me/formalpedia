-- Prove2me | Theorems.Thm_GlobalTheory_UnifParts_exists_inGenus
-- name    : GlobalTheory.UnifParts.exists_inGenus
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:24:28.571806+00:00
-- url     : https://prove2.me/theorems/60f83535-af2d-471f-bc5c-55fa4cd74a72
-- title:
--   Unif Parts: exists in Genus
-- statement:
--   The Unif Parts construction uses the exists in Genus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FamilyUnifOfParts.lean#L61-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FamilyUnifOfParts.lean#L61-L85

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FamilyUnifOfParts
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
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.UnifParts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem GlobalTheory.UnifParts.exists_inGenus (D : Datum H) (l : Level H) (σ : KA l →+* ℂ)
    (hs : ∀ (l : Level H) (N : ℕ) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) → (l.A : ℤ) ∣ ν - 1 →
      ∃ g : Sim D, (N : ℤ) ∣ g.ν N - ν) : ∃ t, InGenus D l σ D t := by sorry
