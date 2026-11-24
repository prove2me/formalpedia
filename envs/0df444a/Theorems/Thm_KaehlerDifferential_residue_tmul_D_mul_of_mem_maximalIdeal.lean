-- Prove2me | Theorems.Thm_KaehlerDifferential_residue_tmul_D_mul_of_mem_maximalIdeal
-- name    : KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:42.560362+00:00
-- url     : https://prove2.me/theorems/7ee79554-3a84-43cd-8e73-0ccd362de4db
-- title:
--   Kaehler Differential: residue tmul D mul of mem maximal Ideal
-- statement:
--   The Kaehler Differential construction uses the residue tmul D mul of mem maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/SpanSingletonProduct.lean#L124-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/SpanSingletonProduct.lean#L124-L141

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KaehlerDifferential

theorem KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal (k : Type*) [CommRing k] (A : Type*)
    [CommRing A]
    [Algebra k A] [IsLocalRing A] (x c : A) (hx : x ∈ IsLocalRing.maximalIdeal A) :
    (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (x * c) =
      IsLocalRing.residue A c •
        ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A x) := by sorry
