-- Prove2me | Theorems.Thm_GlobalTheory_TamePairing_tame_pairing
-- name    : GlobalTheory.TamePairing.tame_pairing
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:02:12.533377+00:00
-- url     : https://prove2.me/theorems/a962e2e7-4182-48ad-95c7-2fe457159c92
-- title:
--   Tame Pairing: tame pairing
-- statement:
--   The Tame Pairing construction uses the tame pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TamePairing.lean#L154-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TamePairing.lean#L154-L300

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TamePairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory GlobalTheory.TamePairing
open GlobalTheory.TameQuot
open NumberField IsDedekindDomain
open scoped Pointwise

theorem GlobalTheory.TamePairing.tame_pairing : _root_.GlobalTheory.Published.TameLocal → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → _root_.Formalism.ConjugateSelfDual.normV v ≡ 1 [MOD l ^ 1] → (∀ g : _root_.ReciprocityTheory.Gal.Dec (F := F) A, _root_.ReciprocityTheory.Gal.cycMod F Ω l 1 g = 1) → ∀ e : _root_.ReciprocityTheory.Gal.H2 (_root_.GlobalTheory.Published.PoitouTate.muLoc F l 1 A) →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1), Function.Bijective e → ∀ (M : ℕ), 1 ≤ M → ∀ d : _root_.Formalism.ConjugateSelfDual.G F Ω →* Multiplicative (ZMod (l ^ M)), IsOpen (d.ker : Set (_root_.Formalism.ConjugateSelfDual.G F Ω)) → ∀ γ φ : _root_.ReciprocityTheory.Gal.Dec (F := F) A, (γ : _root_.Formalism.ConjugateSelfDual.G F Ω) ∈ _root_.ReciprocityTheory.Gal.Ine (F := F) A → d γ = Multiplicative.ofAdd 1 → _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV v) (φ : _root_.Formalism.ConjugateSelfDual.G F Ω) → ∃ u : (ZMod (l ^ 1))ˣ, ∀ z y : _root_.ReciprocityTheory.Gal.Dec (F := F) A → ZMod (l ^ 1), Continuous z → Continuous y → (∀ g h, z (g * h) = z g + z h) → (∀ g h, y (g * h) = y g + y h) → (∀ g : _root_.ReciprocityTheory.Gal.Dec (F := F) A, (g : _root_.Formalism.ConjugateSelfDual.G F Ω) ∈ _root_.ReciprocityTheory.Gal.Ine (F := F) A → y g = 0) → ∀ w : _root_.ReciprocityTheory.Gal.Z2 (_root_.GlobalTheory.Published.PoitouTate.muLoc F l 1 A), (∀ g h, w.1 (g, h) = z g * y h) → e (Submodule.Quotient.mk w) = (u : ZMod (l ^ 1)) * (z γ * y φ) := by sorry
