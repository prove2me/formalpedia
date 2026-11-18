-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RationalFiber_finite_refinement_import
-- name    : OAI.ElementaryPositivity.RationalFiber.finite_refinement_import
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:19:44.005431+00:00
-- url     : https://prove2.me/theorems/44f862ab-842b-4212-be21-a335e0713576
-- title:
--   OAI.ElementaryPositivity.RationalFiber.finite_refinement_import: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RationalFiber.finite_refinement_import` of [lean/OAI/Combinatorics/Chromatic/Walls/FiniteRefinementImportAll.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/FiniteRefinementImportAll.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RationalFiber`, with `open QuantumTorus PowerSeries`):
--
--   ```lean
--   lemma finite_refinement_import
--       (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
--       (D : ℕ) (l : List (ComparisonCrossing v Ω δ k B))
--       (href : ∀N,∃l',WordRefines v Ω δ k B D l l' ∧ ∀n≤N,
--         coeff n (comparisonWordOld v Ω hΩ δ k p hp hδ B l').val.val=coeff n 1)
--       (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
--       coeff D (comparisonWordAction v Ω hΩ δ k p hp B l f)=coeff D f
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.Torus`, `OAI.ElementaryPositivity.QuantumTorus.biSupportedSubring`, `OAI.ElementaryPositivity.QuantumTorus.laurentCompletionRing`, `OAI.ElementaryPositivity.RationalFiber.FiberTorus`, `OAI.ElementaryPositivity.RationalFiber.complementAlpha`, `OAI.ElementaryPositivity.RationalFiber.complementOmega` and `OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.RationalFiber.ComparisonCrossing` and `OAI.ElementaryPositivity.RationalFiber.WordRefines` (definitions bundle `OAIQ368Chrom005` of this split); `OAI.ElementaryPositivity.RationalFiber.comparisonWordAction` and `OAI.ElementaryPositivity.RationalFiber.comparisonWordOld` (definitions bundle `OAIQ368Chrom008` of this split); `OAI.ElementaryPositivity.RationalFiber.instRingTorus_9` (definitions bundle `OAIQ368Chrom009` of this split).
--
--   **Used by.** The proofs of `OAI.ElementaryPositivity.QuantumTorus.halfspace_canonical_polynomial_coefficients`, `OAI.ElementaryPositivity.QuantumTorus.mutatedIncoming_probe`, `OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_canonical`, `OAI_ElementaryPositivity_QuantumTorus_mutatedTransport_eq_path`, `OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming_mutation` and `OAI.ElementaryPositivity.RationalFiber.actualPath_rational_loop_coefficient` of this split import it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/FiniteRefinementImportAll.lean (declaration OAI.ElementaryPositivity.RationalFiber.finite_refinement_import)

import Mathlib
import Definitions.Def_OAIQ368Chrom008
import Definitions.Def_OAIQ368Chrom009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (hδ : δ p=0) (B : ℕ)
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_9
local instance instAddCommMonoidTorus_6_r4beb23_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_6_r4beb23_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_9_r4beb23_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_9_r4beb23_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma finite_refinement_import
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (D : ℕ) (l : List (ComparisonCrossing v Ω δ k B))
    (href : ∀N,∃l',WordRefines v Ω δ k B D l l' ∧ ∀n≤N,
      coeff n (comparisonWordOld v Ω hΩ δ k p hp hδ B l').val.val=coeff n 1)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    coeff D (comparisonWordAction v Ω hΩ δ k p hp B l f)=coeff D f := by
  sorry

end
end ElementaryPositivity.RationalFiber

end

end OAI
end
