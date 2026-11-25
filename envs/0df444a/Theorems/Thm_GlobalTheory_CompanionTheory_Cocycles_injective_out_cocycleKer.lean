-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Cocycles_injective_out_cocycleKer
-- name    : GlobalTheory.CompanionTheory.Cocycles.injective_out_cocycleKer
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:59:38.957575+00:00
-- url     : https://prove2.me/theorems/10b15236-4e90-5267-a289-2e4b7a2fcc52
-- title:
--   Cocycles: injective out cocycle Ker
-- statement:
--   The Cocycles construction uses the injective out cocycle Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/FiniteContinuousCrossedHomomorphisms.lean#L55-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/FiniteContinuousCrossedHomomorphisms.lean#L55-L63

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

theorem GlobalTheory.CompanionTheory.Cocycles.injective_out_cocycleKer (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) :
    Function.Injective fun q : G ⧸ cocycleKer ρ f hf =>
      ((f q.out, ⇑(ρ q.out)) : V × (V → V)) := by sorry
