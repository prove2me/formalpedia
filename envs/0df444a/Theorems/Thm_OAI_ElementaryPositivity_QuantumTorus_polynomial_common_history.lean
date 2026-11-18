-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_polynomial_common_history
-- name    : OAI.ElementaryPositivity.QuantumTorus.polynomial_common_history
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T19:01:36.658521+00:00
-- url     : https://prove2.me/theorems/d0c4741c-a82e-44ce-a57f-db1973e4f36d
-- title:
--   OAI.ElementaryPositivity.QuantumTorus.polynomial_common_history: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.QuantumTorus.polynomial_common_history` of [lean/OAI/Combinatorics/Chromatic/Histories/CommonHistoryLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Histories/CommonHistoryLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.QuantumTorus`, with `open PowerSeries PowerSeriesAdjoint WallUnits HahnSeries`, `open Classical`):
--
--   ```lean
--   lemma polynomial_common_history (b:M) (hb:rootOrder coord b=0)
--       (N:ℕ) (r:M) (hr:HasRootDegree C N (r-b)) :
--       ∃p:LocalHistoryFormula M E,
--         p.Positive Ω C e (simpleTotalTransport Ω C) ∧ p.Bounded C b N ∧
--         ∀F:Torus LaurentRay.vUnit Ω,
--           (∀m,F m≠0 → ∃d,HasRootDegree C d (m-b)) →
--           F r=∑l:p.Leaf,p.leafWeight Ω C e (simpleTotalTransport Ω C) l *
--             polynomialSectionIncoming Ω C coord F (p.leafExponent l)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.HasRootDegree`, `OAI.ElementaryPositivity.QuantumTorus.Torus` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.QuantumTorus.rootOrder` (definitions bundle `OAIQ368Chrom002` of this split); `OAI.ElementaryPositivity.QuantumTorus.simpleTotalTransport` (definitions bundle `OAIQ368Chrom008` of this split); `OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming` (definitions bundle `OAIQ368Chrom057` of this split); `OAI.ElementaryPositivity.QuantumTorus.LocalHistoryFormula`, `OAI.ElementaryPositivity.QuantumTorus.LocalHistoryFormula.Bounded`, `OAI.ElementaryPositivity.QuantumTorus.LocalHistoryFormula.Leaf`, `OAI.ElementaryPositivity.QuantumTorus.LocalHistoryFormula.Positive`, `OAI.ElementaryPositivity.QuantumTorus.LocalHistoryFormula.leafExponent`, `OAI.ElementaryPositivity.QuantumTorus.LocalHistoryFormula.leafFintype` and `OAI.ElementaryPositivity.QuantumTorus.LocalHistoryFormula.leafWeight` (definitions bundle `OAIQ368Chrom058` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.TriangularDynamics.graph_common_history` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Histories/CommonHistoryLeaves.lean (declaration OAI.ElementaryPositivity.QuantumTorus.polynomial_common_history)

import Mathlib
import Definitions.Def_OAIQ368Chrom058

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits HahnSeries
open Classical
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d)

variable (e:M →+ E) (he:Function.Injective e)
variable (B:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB:∀x,B x x=0)
variable (hcomp:∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.commonHistoryLeavesRing
local instance commonHistoryLeavesAddCommMonoid_rc9266d_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance commonHistoryLeavesAddGroup_rc9266d_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hΩ hcoord he hB hcomp hdeg in
lemma polynomial_common_history (b:M) (hb:rootOrder coord b=0)
    (N:ℕ) (r:M) (hr:HasRootDegree C N (r-b)) :
    ∃p:LocalHistoryFormula M E,
      p.Positive Ω C e (simpleTotalTransport Ω C) ∧ p.Bounded C b N ∧
      ∀F:Torus LaurentRay.vUnit Ω,
        (∀m,F m≠0 → ∃d,HasRootDegree C d (m-b)) →
        F r=∑l:p.Leaf,p.leafWeight Ω C e (simpleTotalTransport Ω C) l *
          polynomialSectionIncoming Ω C coord F (p.leafExponent l) := by
  sorry
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end
