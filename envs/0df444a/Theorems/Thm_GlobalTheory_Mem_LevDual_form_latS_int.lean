-- Prove2me | Theorems.Thm_GlobalTheory_Mem_LevDual_form_latS_int
-- name    : GlobalTheory.Mem.LevDual.form_latS_int
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-27T05:39:21.513921+00:00
-- url     : https://prove2.me/theorems/3c82debf-8d25-4d12-808b-26665a5c4d30
-- title:
--   Lev Dual: form lat S int
-- statement:
--   The Lev Dual construction uses the form lat S int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UnitaryCarryDual.lean#L36-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UnitaryCarryDual.lean#L36-L70

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem GlobalTheory.Mem.LevDual.form_latS_int (σ : E →ₐ[F] E) {n : ℕ} (L' : Submodule (𝓞 E) (Fin n → E))
    (z : Fin n → E) (hz : z ∈ dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) L')
    (u : Fin n → E ⊗[F] 𝔸)
    (hu : u ∈ latS (F := F) 𝔸 (tensInt (F := F) 𝔸 (intOE E) (intAd F)) L') :
    (fun i => sigR σ 𝔸 (u i)) ⬝ᵥ (fun a => inclE (F := F) 𝔸 (z a)) ∈
      tensInt (F := F) 𝔸 (intOE E) (intAd F) := by sorry
