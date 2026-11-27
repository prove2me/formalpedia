-- Prove2me | Theorems.Thm_GlobalTheory_exists_eq_of_locally_fraction_on_generisations
-- name    : GlobalTheory.exists_eq_of_locally_fraction_on_generisations
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:45:05.670838+00:00
-- url     : https://prove2.me/theorems/eda353de-7223-4ccc-8bc1-c836bf5d6ea3
-- title:
--   Global Theory: exists eq of locally fraction on generisations
-- statement:
--   The Global Theory construction uses the exists eq of locally fraction on generisations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEqOfLocallyFractionOnGenerisations.lean#L5-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsEqOfLocallyFractionOnGenerisations.lean#L5-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsEqOfLocallyFractionOnGenerisations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_eq_of_locally_fraction_on_generisations
    (K : Type) [Field K] (R : Type) [CommRing R] [IsNoetherianRing R] [Algebra K R]
    (W : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k], (R →ₐ[K] k) → k)
    (hW : ∀ (q : Ideal R) [q.IsPrime], ∃ a : Localization.AtPrime q,
      ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : Localization.AtPrime q →ₐ[K] k),
        W k (φ.comp (IsScalarTower.toAlgHom K R (Localization.AtPrime q))) = φ a) :
    ∃ r : R, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : R →ₐ[K] k),
      W k φ = φ r := by sorry
