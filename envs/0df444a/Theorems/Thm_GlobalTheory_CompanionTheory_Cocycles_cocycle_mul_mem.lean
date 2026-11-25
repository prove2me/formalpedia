-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Cocycles_cocycle_mul_mem
-- name    : GlobalTheory.CompanionTheory.Cocycles.cocycle_mul_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:52:47.540154+00:00
-- url     : https://prove2.me/theorems/4e9a7ed8-84c6-4019-a3c6-a9725665e729
-- title:
--   Cocycles: cocycle mul mem
-- statement:
--   The Cocycles construction uses the cocycle mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/FiniteContinuousCrossedHomomorphisms.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/FiniteContinuousCrossedHomomorphisms.lean#L44-L47

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

theorem GlobalTheory.CompanionTheory.Cocycles.cocycle_mul_mem (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) (g : G) {c : G}
    (hc : c ∈ cocycleKer ρ f hf) : f (g * c) = f g := by sorry
