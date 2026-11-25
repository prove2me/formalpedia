-- Prove2me | Theorems.Thm_GlobalTheory_SecLimit_IsBas_reduce
-- name    : GlobalTheory.SecLimit.IsBas.reduce
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:29:34.038242+00:00
-- url     : https://prove2.me/theorems/14ae41aa-4ef3-5fe5-b779-4a7fb2e6528e
-- title:
--   Is Bas: reduce
-- statement:
--   The Is Bas construction uses the reduce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueLimit.lean#L57-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueLimit.lean#L57-L93

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.SecLimit
universe u
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {W W' W'' : Type u} [CommRing W] [CommRing W']
  [CommRing W''] {m : ℕ}

theorem GlobalTheory.SecLimit.IsBas.reduce {c : R →+* W} {c' : R' →+* W'} {c'' : R'' →+* W''} {ρ : W →+* W'} {ρ' : W' →+* W''}
    {g : R →+* R'} {g' : R' →+* R''} [IsLocalHom g'] (h : ∀ a, ρ (c a) = c' (g a)) (h' : ∀ a, ρ' (c' a) = c'' (g' a))
    {S : Set W} {S' : Set W'} {S'' : Set W''} (hS : ∀ s ∈ S, ρ s ∈ S') (hS' : ∀ s ∈ S', ρ' s ∈ S'')
    (hl : ∀ s ∈ S'', ∃ t ∈ S, s = ρ' (ρ t)) {b : Fin m → W} {b' : Fin m → W'} {b'' : Fin m → W''}
    (hb : IsBas c S b) (hb' : IsBas c' S' b') (hb'' : IsBas c'' S'' b'') : IsBas c' S' (fun i => ρ (b i)) := by sorry
