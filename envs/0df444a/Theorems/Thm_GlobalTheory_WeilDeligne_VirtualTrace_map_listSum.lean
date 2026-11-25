-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_VirtualTrace_map_listSum
-- name    : GlobalTheory.WeilDeligne.VirtualTrace.map_listSum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T17:15:58.698492+00:00
-- url     : https://prove2.me/theorems/97ed7c1a-1645-43bc-ac15-7b2f9750f4e5
-- title:
--   Virtual Trace: map list Sum
-- statement:
--   The Virtual Trace construction uses the map list Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MultiplicativeVirtualCharacter.lean#L55-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MultiplicativeVirtualCharacter.lean#L55-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_Mono0OfLpDimEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyEqOfTracePowersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MultiplicativeVirtualCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.VirtualTrace
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem GlobalTheory.WeilDeligne.VirtualTrace.map_listSum {M : Type} [CommGroup M] (f : WD h → M)
    (hf : ∀ x y, f (x.lpSum y) = f x * f y) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    f (WD.mk (listSum h L).2) = (L.map fun x => f (WD.mk x.2)).prod := by sorry
