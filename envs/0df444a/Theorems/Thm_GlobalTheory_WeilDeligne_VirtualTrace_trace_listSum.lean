-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_VirtualTrace_trace_listSum
-- name    : GlobalTheory.WeilDeligne.VirtualTrace.trace_listSum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:15:18.555372+00:00
-- url     : https://prove2.me/theorems/b926ffd3-4f69-45fd-8eae-f3c195b38a72
-- title:
--   Virtual Trace: trace list Sum
-- statement:
--   The Virtual Trace construction uses the trace list Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MultiplicativeVirtualCharacter.lean#L31-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MultiplicativeVirtualCharacter.lean#L31-L47

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

theorem GlobalTheory.WeilDeligne.VirtualTrace.trace_listSum (σ : Weil h) (k : ℕ) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    LinearMap.trace ℂ _ ((listSum h L).2.ρ σ ^ k) =
      (L.map fun x => LinearMap.trace ℂ _ (x.2.ρ σ ^ k)).sum := by sorry
