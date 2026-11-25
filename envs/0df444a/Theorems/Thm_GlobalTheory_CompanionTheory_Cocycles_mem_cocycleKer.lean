-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Cocycles_mem_cocycleKer
-- name    : GlobalTheory.CompanionTheory.Cocycles.mem_cocycleKer
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:31:28.564867+00:00
-- url     : https://prove2.me/theorems/e8387713-8d1b-4d15-a71d-a8cda8ddc2d8
-- title:
--   Cocycles: mem cocycle Ker
-- statement:
--   The Cocycles construction uses the mem cocycle Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/FiniteContinuousCrossedHomomorphisms.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/FiniteContinuousCrossedHomomorphisms.lean#L40-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_FiniteContinuousCrossedHomomorphisms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Cocycles
variable {k G V : Type} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V} {f : G → V}

theorem GlobalTheory.CompanionTheory.Cocycles.mem_cocycleKer (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) (g : G) :
    g ∈ cocycleKer ρ f hf ↔ ρ g = 1 ∧ f g = 0 := by sorry
