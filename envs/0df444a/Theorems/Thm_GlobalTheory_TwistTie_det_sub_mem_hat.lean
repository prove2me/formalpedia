-- Prove2me | Theorems.Thm_GlobalTheory_TwistTie_det_sub_mem_hat
-- name    : GlobalTheory.TwistTie.det_sub_mem_hat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:59.558805+00:00
-- url     : https://prove2.me/theorems/9afe8139-b3f8-4bb1-b1c9-d4d659b15b6e
-- title:
--   Twist Tie: det sub mem hat
-- statement:
--   The Twist Tie construction uses the det sub mem hat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/DetSubMemOfConj.lean#L106-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/DetSubMemOfConj.lean#L106-L198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_DetSubMemOfConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TwistTie
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.TwistTie.det_sub_mem_hat {n : ℕ} {La : Type} [AddCommGroup La] [Module (𝓞 E) La] [Module.Finite (𝓞 E) La]
    (ι : La →ₗ[𝓞 E] (Fin n → E)) (hsp : Submodule.span E (Set.range ι) = ⊤) (I : Ideal (𝓞 E)) (hI : I ≠ ⊤)
    (v : Fin n → La) (hv : (⊤ : Submodule (𝓞 E) La) ≤ Submodule.span (𝓞 E) (Set.range v) ⊔ I • ⊤)
    (s : La →ₗ[𝓞 E] La) (N : ℕ) (hN : (N : 𝓞 E) ∈ I) (G : Matrix (Fin n) (Fin n) (RA F E))
    (hG : G.det ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)))
    (h : ∀ j, ∃ w ∈ hat F (Set.range ι), G *ᵥ fv F (ι (v j)) - fv F (ι (s (v j))) = N • w) :
    ∃ a : Matrix (Fin n) (Fin n) (𝓞 E), (∀ j, s (v j) - ∑ i, a i j • v i ∈ (I • ⊤ : Submodule (𝓞 E) La)) ∧
      G.det - 1 ⊗ₜ ((a.det : 𝓞 E) : E) ∈ hat1 F (algebraMap (𝓞 E) E '' (I : Set (𝓞 E))) := by sorry
