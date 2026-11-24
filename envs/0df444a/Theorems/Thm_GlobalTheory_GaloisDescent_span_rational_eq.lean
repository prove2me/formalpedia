-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_span_rational_eq
-- name    : GlobalTheory.GaloisDescent.span_rational_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:48:36.545315+00:00
-- url     : https://prove2.me/theorems/0010cafc-9f90-45fd-ace6-940afe1abb59
-- title:
--   Galois Descent: span rational eq
-- statement:
--   The Galois Descent construction uses the span rational eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L67-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L67-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L M G ι : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module L M]

theorem GlobalTheory.GaloisDescent.span_rational_eq (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (b : Basis ι L M) (φ : G → M →+ M) (hφ : ∀ g a i, φ g (a • b i) = s g a • b i)
    (W : Submodule L M) (hW : ∀ g, ∀ w ∈ W, φ g w ∈ W) :
    Submodule.span L {u | u ∈ W ∧ ∀ i, b.repr u i ∈ Set.range (algebraMap K L)} = W := by sorry
