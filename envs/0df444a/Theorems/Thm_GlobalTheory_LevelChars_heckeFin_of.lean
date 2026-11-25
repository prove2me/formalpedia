-- Prove2me | Theorems.Thm_GlobalTheory_LevelChars_heckeFin_of
-- name    : GlobalTheory.LevelChars.heckeFin_of
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:09.286743+00:00
-- url     : https://prove2.me/theorems/bcc91d80-8abf-5989-b32c-5514377b340c
-- title:
--   Level Chars: hecke Fin of
-- statement:
--   The Level Chars construction uses the hecke Fin of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteChars.lean#L64-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteChars.lean#L64-L89

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteChars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.LevelChars

theorem GlobalTheory.LevelChars.heckeFin_of
    (hA : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (ψ : Formalism.L2.Host.HChar L),
      (∀ k : Lˣ, ψ.inf k = 1) → (∀ v, v ∉ S → ψ.UnrAt v) → (∀ v ∈ S, ψ.LevelLe v N) → ∀ a ∈ levSub L S N, ψ.1 a = 1)
    (hC : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N).FiniteIndex) :
    ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ)
    (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
    {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧ ∀ v ∈ S, χ.LevelLe v N}.Finite := by sorry
