-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Cocycles_inv_mul_mem_cocycleKer
-- name    : GlobalTheory.CompanionTheory.Cocycles.inv_mul_mem_cocycleKer
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:53:21.795201+00:00
-- url     : https://prove2.me/theorems/adc39cf5-e5a0-49a9-b3df-a3ac2e71ad07
-- title:
--   Cocycles: inv mul mem cocycle Ker
-- statement:
--   The Cocycles construction uses the inv mul mem cocycle Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/FiniteContinuousCrossedHomomorphisms.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/FiniteContinuousCrossedHomomorphisms.lean#L49-L53

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

theorem GlobalTheory.CompanionTheory.Cocycles.inv_mul_mem_cocycleKer (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) {a b : G}
    (h1 : f a = f b) (h2 : ρ a = ρ b) : a⁻¹ * b ∈ cocycleKer ρ f hf := by sorry
