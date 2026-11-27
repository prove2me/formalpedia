-- Prove2me | Theorems.Thm_GlobalTheory_Mem_LevDual_unitary_carry_dual
-- name    : GlobalTheory.Mem.LevDual.unitary_carry_dual
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T05:37:52.343907+00:00
-- url     : https://prove2.me/theorems/3ba32f71-26f9-5d08-95ab-f78eb56f98fa
-- title:
--   Lev Dual: unitary carry dual
-- statement:
--   The Lev Dual construction uses the unitary carry dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UnitaryCarryDual.lean#L201-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UnitaryCarryDual.lean#L201-L361

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UnitaryCarryDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.LevDual
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

theorem GlobalTheory.Mem.LevDual.unitary_carry_dual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (p : 𝓞 E), J = 1 → p ≠ 0 → (∀ x, x ∈ L ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → p ∣ r)) → ∀ (L' : Submodule (𝓞 E) (Fin n → E)) (Y : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))), Y ∈ _root_.Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ x : Fin n → TensorProduct F E (FiniteAdeleRing (𝓞 F) F), x ∈ _root_.Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.intOE E) (_root_.Formalism.UG.intAd F)) L' ↔ ((Y⁻¹ : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) : Matrix (Fin n) (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) *ᵥ x ∈ _root_.Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.intOE E) (_root_.Formalism.UG.intAd F)) L) → ∀ z ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) J L', ((_root_.Formalism.UG.bc (_root_.Formalism.UG.prV (E := E) w) Y)⁻¹).1 *ᵥ (fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (z a)) ∈ _root_.Formalism.UG.latS (F := F) (w.adicCompletion F) (_root_.Formalism.BasicNotions.intV E w) (Submodule.span (𝓞 E) (_root_.Formalism.BasicNotions.dualSet (σ : E →+* E) J L)) := by sorry
