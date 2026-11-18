-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_section_line_program
-- name    : OAI.ElementaryPositivity.QuantumTorus.section_line_program
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:10:03.484645+00:00
-- url     : https://prove2.me/theorems/8266aaf7-aee8-4f5f-84aa-0ed17e0248c5
-- title:
--   OAI.ElementaryPositivity.QuantumTorus.section_line_program: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.QuantumTorus.section_line_program` of [lean/OAI/Combinatorics/Chromatic/Walls/SectionLineProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/SectionLineProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.QuantumTorus`, with `open PowerSeries PowerSeriesAdjoint PowerSeriesSplit FiniteRayGeometry FiniteEventTraversal LaurentPositive WallUnits`, `open scoped BigOperators`, `open Classical`):
--
--   ```lean
--   lemma section_line_program (F:CompletedPositive LaurentRay.vUnit Ω C)
--       (N:ℕ) (walls:WallsPositiveThrough Ω C e N F) (h:Module.Dual ℝ E) (r:M) :
--       ∃ts:List (LineTransfer E),
--         (∀t∈ts,t.PositiveThrough Ω C e F N r) ∧
--         ∀b (X:PowerSeries (Torus LaurentRay.vUnit Ω)),ShiftGraded LaurentRay.vUnit Ω C b X →
--           coeff N (sectionValue LaurentRay.vUnit Ω C F (h.toAddMonoidHom.comp e) X) r =
--           coeff N (sectionValue LaurentRay.vUnit Ω C F (incomingCovector Ω r) X) r +
--             (ts.map (fun t=>t.delta Ω C e F b X N r)).sum
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.CompletedPositive`, `OAI.ElementaryPositivity.QuantumTorus.HasRootDegree`, `OAI.ElementaryPositivity.QuantumTorus.Torus`, `OAI.ElementaryPositivity.QuantumTorus.incomingCovector`, `OAI.ElementaryPositivity.QuantumTorus.Torus.instRing` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.QuantumTorus.ShiftGraded`, `OAI.ElementaryPositivity.QuantumTorus.WallsPositiveThrough` and `OAI.ElementaryPositivity.QuantumTorus.sectionValue` (definitions bundle `OAIQ368Chrom013` of this split); `OAI.ElementaryPositivity.QuantumTorus.LineTransfer`, `OAI.ElementaryPositivity.QuantumTorus.LineTransfer.PositiveThrough` and `OAI.ElementaryPositivity.QuantumTorus.LineTransfer.delta` (definitions bundle `OAIQ368Chrom015` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.QuantumTorus.polynomial_common_history` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/SectionLineProgram.lean (declaration OAI.ElementaryPositivity.QuantumTorus.section_line_program)

import Mathlib
import Definitions.Def_OAIQ368Chrom015

section

attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit FiniteRayGeometry FiniteEventTraversal LaurentPositive WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)
variable (e:M →+ E) (he:Function.Injective e)
variable (B:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB:∀x,B x x=0)
variable (hcomp:∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in

lemma section_line_program (F:CompletedPositive LaurentRay.vUnit Ω C)
    (N:ℕ) (walls:WallsPositiveThrough Ω C e N F) (h:Module.Dual ℝ E) (r:M) :
    ∃ts:List (LineTransfer E),
      (∀t∈ts,t.PositiveThrough Ω C e F N r) ∧
      ∀b (X:PowerSeries (Torus LaurentRay.vUnit Ω)),ShiftGraded LaurentRay.vUnit Ω C b X →
        coeff N (sectionValue LaurentRay.vUnit Ω C F (h.toAddMonoidHom.comp e) X) r =
        coeff N (sectionValue LaurentRay.vUnit Ω C F (incomingCovector Ω r) X) r +
          (ts.map (fun t=>t.delta Ω C e F b X N r)).sum := by
  sorry
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end
