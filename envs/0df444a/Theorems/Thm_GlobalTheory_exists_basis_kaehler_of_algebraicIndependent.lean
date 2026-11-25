-- Prove2me | Theorems.Thm_GlobalTheory_exists_basis_kaehler_of_algebraicIndependent
-- name    : GlobalTheory.exists_basis_kaehler_of_algebraicIndependent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:34.820617+00:00
-- url     : https://prove2.me/theorems/8a85f0cf-6a1c-4d5a-8e8d-ee72aaf3b826
-- title:
--   Global Theory: exists basis kaehler of algebraic Independent
-- statement:
--   The Global Theory construction uses the exists basis kaehler of algebraic Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L439-L463
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L439-L463

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
open scoped IntermediateField.algebraAdjoinAdjoin

theorem GlobalTheory.exists_basis_kaehler_of_algebraicIndependent {K F ι : Type*} [Field K] [Field F]
    [Algebra K F] {v : ι → F} (hv : AlgebraicIndependent K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) F] :
    ∃ b : Basis ι F Ω[F⁄K], ∀ i, b i = D K F (v i) := by sorry
