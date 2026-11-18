-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_genuine_history_cut_deficit
-- name    : OAI.ElementaryPositivity.TriangularDynamics.genuine_history_cut_deficit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:25:08.863537+00:00
-- url     : https://prove2.me/theorems/9e68bb1f-4f2c-400d-aec2-193a61bf3e94
-- title:
--   OAI.ElementaryPositivity.TriangularDynamics.genuine_history_cut_deficit: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.TriangularDynamics.genuine_history_cut_deficit` of [lean/OAI/Combinatorics/Chromatic/Walls/TriangularPeriodTransport.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularPeriodTransport.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.TriangularDynamics`, with `open QuantumTorus WallUnits`, `open Classical`):
--
--   ```lean
--   lemma genuine_history_cut_deficit (is:List I) (his:is.Nodup) (hall:∀i,i∈is)
--       (ch:FreeChart (I:=I) e)
--       (hinv:(is.map (simpleRoot ch.roots)).Perm
--         (forwardInventory (h ∘ anchor) (h ∘ periodBridge 0) (phaseCycle n)))
--       {N:ℕ} (f:ElementaryExpr N) (m:Lattice n (Cell n))
--       (hm:polynomialSectionIncoming Ω ch.roots ch.coord
--         (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ periodBridge 0))) (h m)≠0)
--       (L:ℕ) (i:Fin n) :
--       0 ≤ cutDeficit cellLevel i N L (history (triangularOmega n) cellLevel (phaseCycle n) m L)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.simpleRoot` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr`, `OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming`, `OAI.ElementaryPositivity.TriangularDynamics.Cell`, `OAI.ElementaryPositivity.TriangularDynamics.FreeChart`, `OAI.ElementaryPositivity.TriangularDynamics.Lattice`, `OAI.ElementaryPositivity.TriangularDynamics.Vertex`, `OAI.ElementaryPositivity.TriangularDynamics.anchor`, `OAI.ElementaryPositivity.TriangularDynamics.cellLevel`, `OAI.ElementaryPositivity.TriangularDynamics.cutDeficit`, `OAI.ElementaryPositivity.TriangularDynamics.forwardInventory`, `OAI.ElementaryPositivity.TriangularDynamics.history`, `OAI.ElementaryPositivity.TriangularDynamics.periodBridge`, `OAI.ElementaryPositivity.TriangularDynamics.phaseCycle`, `OAI.ElementaryPositivity.TriangularDynamics.triangularOmega`, `OAI.ElementaryPositivity.TriangularDynamics.vertexDisplay` and `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr.eval` (definitions bundle `OAIQ368Chrom057` of this split).
--
--   **Used by.** The proofs of `OAI_ElementaryPositivity_TriangularDynamics_triangularExpression_anchorSupported`, `OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_locality`, `OAI_ElementaryPositivity_TriangularDynamics_triangularLinear_theta`, `OAI.ElementaryPositivity.TriangularDynamics.triangularMonomial_initial`, `OAI.ElementaryPositivity.TriangularDynamics.triangularPower_positive`, `OAI.ElementaryPositivity.TriangularDynamics.triangularPureIncoming_delta` and `OAI.ElementaryPositivity.TriangularDynamics.triangularPure_equal` of this split import it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularPeriodTransport.lean (declaration OAI.ElementaryPositivity.TriangularDynamics.genuine_history_cut_deficit)

import Mathlib
import Definitions.Def_OAIQ368Chrom057

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits
open Classical
noncomputable section
variable {n:ℕ} {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (hnd:∀r≠0,∃m,Ω r m≠0)
variable (h:Lattice n (Cell n) →+ M) (hform:∀x y,Ω (h x) (h y)=triangularOmega n x y)
variable (retract:M →+ Lattice n (Cell n)) (hret:∀m,retract (h m)=m)

include hΩ he hS hcomp hnd hform hret in
lemma genuine_history_cut_deficit (is:List I) (his:is.Nodup) (hall:∀i,i∈is)
    (ch:FreeChart (I:=I) e)
    (hinv:(is.map (simpleRoot ch.roots)).Perm
      (forwardInventory (h ∘ anchor) (h ∘ periodBridge 0) (phaseCycle n)))
    {N:ℕ} (f:ElementaryExpr N) (m:Lattice n (Cell n))
    (hm:polynomialSectionIncoming Ω ch.roots ch.coord
      (f.eval LaurentRay.vUnit Ω (vertexDisplay (h ∘ anchor) (h ∘ periodBridge 0))) (h m)≠0)
    (L:ℕ) (i:Fin n) :
    0 ≤ cutDeficit cellLevel i N L (history (triangularOmega n) cellLevel (phaseCycle n) m L) := by
  sorry
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end
