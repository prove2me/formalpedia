-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Cocycles_isOpen_cocycleKer
-- name    : GlobalTheory.CompanionTheory.Cocycles.isOpen_cocycleKer
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:59:46.468819+00:00
-- url     : https://prove2.me/theorems/451b437a-535a-5f1a-a0ad-8629c95a3749
-- title:
--   Cocycles: is Open cocycle Ker
-- statement:
--   The Cocycles construction uses the is Open cocycle Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/FiniteContinuousCrossedHomomorphisms.lean#L87-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/FiniteContinuousCrossedHomomorphisms.lean#L87-L99

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

theorem GlobalTheory.CompanionTheory.Cocycles.isOpen_cocycleKer {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A] [Finite A.V] {f : G → A.V}
    (hlc : IsLocallyConstant f) (hf : ∀ g h : G, f (g * h) = f g + A.ρ g (f h)) :
    IsOpen (cocycleKer A.ρ f hf : Set G) := by sorry
