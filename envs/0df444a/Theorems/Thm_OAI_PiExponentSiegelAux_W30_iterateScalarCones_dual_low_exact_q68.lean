-- Prove2me | Theorems.Thm_OAI_PiExponentSiegelAux_W30_iterateScalarCones_dual_low_exact_q68
-- name    : OAI.PiExponentSiegelAux.W30.iterateScalarCones_dual_low_exact_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:21:28.467603+00:00
-- url     : https://prove2.me/theorems/7422817f-514f-481e-8034-e2f53683725d
-- title:
--   OAI.PiExponentSiegelAux.W30.iterateScalarCones_dual_low_exact_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponentSiegelAux.W30.iterateScalarCones_dual_low_exact` of [lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceDualExactness.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceDualExactness.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponentSiegelAux.W30`, with `open Module`, `open scoped Pointwise`):
--
--   ```lean
--   theorem iterateScalarCones_dual_low_exact_q68 (rs : List R) (n : ℕ)
--       (P : ChainComplex (ModuleCat.{u} R) ℕ) (I : Ideal R)
--       (e : P.X (n + 1) ≃ₗ[R] R)
--       (hbound : ∀ k, n + 1 < k → Subsingleton (P.X k))
--       (hinj : Function.Injective (P.d 1 0).hom.dualMap)
--       (hlow : ∀ k, k < n → LinearMap.range (P.d (k + 1) k).hom.dualMap =
--         LinearMap.ker (P.d (k + 2) (k + 1)).hom.dualMap)
--       (hI : LinearMap.range
--         ((W31.topDualCoordinate e).toLinearMap.comp (P.d (n + 1) n).hom.dualMap) = I)
--       (hreg : RingTheory.Sequence.IsRegular (R ⧸ I) rs) :
--       ∀ k, k + 1 < n + 1 + rs.length →
--         LinearMap.range ((iterateScalarCones P rs).d (k + 1) k).hom.dualMap =
--           LinearMap.ker ((iterateScalarCones P rs).d (k + 2) (k + 1)).hom.dualMap
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentSiegelAux.W30.iterateScalarCones` (definitions bundle `OAIQ068A009` of this split); `OAI.PiExponentSiegelAux.W31.topDualCoordinate` (definitions bundle `OAIQ068A011` of this split).
--
--   **Used by.** The proof of `OAI.PiExponentSiegel.W58.polynomialLocal_regular_prefix_maximal_not_associated_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceDualExactness.lean (declaration OAI.PiExponentSiegelAux.W30.iterateScalarCones_dual_low_exact)

import Mathlib
import Definitions.Def_OAIQ068A009
import Definitions.Def_OAIQ068A011

section

attribute [-instance] _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegelAux.W30
open Module
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]

theorem iterateScalarCones_dual_low_exact_q68 (rs : List R) (n : ℕ)
    (P : ChainComplex (ModuleCat.{u} R) ℕ) (I : Ideal R)
    (e : P.X (n + 1) ≃ₗ[R] R)
    (hbound : ∀ k, n + 1 < k → Subsingleton (P.X k))
    (hinj : Function.Injective (P.d 1 0).hom.dualMap)
    (hlow : ∀ k, k < n → LinearMap.range (P.d (k + 1) k).hom.dualMap =
      LinearMap.ker (P.d (k + 2) (k + 1)).hom.dualMap)
    (hI : LinearMap.range
      ((W31.topDualCoordinate e).toLinearMap.comp (P.d (n + 1) n).hom.dualMap) = I)
    (hreg : RingTheory.Sequence.IsRegular (R ⧸ I) rs) :
    ∀ k, k + 1 < n + 1 + rs.length →
      LinearMap.range ((iterateScalarCones P rs).d (k + 1) k).hom.dualMap =
        LinearMap.ker ((iterateScalarCones P rs).d (k + 2) (k + 1)).hom.dualMap := by
  sorry

end PiExponentSiegelAux.W30

end

end OAI
end
