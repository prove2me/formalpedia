-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_bd_apply
-- name    : GlobalTheory.CompanionTheory.CasselmanOsborne.bd_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:08.477075+00:00
-- url     : https://prove2.me/theorems/60dfe427-cd6e-4e69-a524-ecda077db39e
-- title:
--   Casselman Osborne: bd apply
-- statement:
--   The Casselman Osborne construction uses the bd apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZetaDegZero.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZetaDegZero.lean#L99-L101

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CasselmanOsborne
open Formalism.REAL (GlRel qdet qminor Tm)
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.CompanionTheory.CasselmanOsborne.bd_apply (E : Fin n → Fin n → Module.End ℂ V) (x : Ch ε V) (A : Finset (NC ε)) :
    bd ε E x A = ∑ i : NC ε, E i.1.1 i.1.2 (if i ∈ A then 0 else sg i A • x (insert i A)) := by sorry
