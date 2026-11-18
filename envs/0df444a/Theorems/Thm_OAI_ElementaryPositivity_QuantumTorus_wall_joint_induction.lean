-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_wall_joint_induction
-- name    : OAI.ElementaryPositivity.QuantumTorus.wall_joint_induction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:08:15.65846+00:00
-- url     : https://prove2.me/theorems/85f9fa3f-4e1e-4f01-b23e-b81035b2dae2
-- title:
--   OAI.ElementaryPositivity.QuantumTorus.wall_joint_induction: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.QuantumTorus.wall_joint_induction` of [lean/OAI/Combinatorics/Chromatic/Walls/PlanarRefinement.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/PlanarRefinement.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.QuantumTorus`, with `open PowerSeries FiniteRayGeometry RootTruncation WallUnits`):
--
--   ```lean
--   theorem wall_joint_induction (n dr : ℕ) (r : M) (hdr : 0 < dr) (hrd : HasRootDegree C dr r)
--       (F : CompletedPositive LaurentRay.vUnit Ω C) (ih : WallsPositiveThrough Ω C e n F)
--       (k : Module.Dual ℝ E)
--       (H : GenericOffset (realRootsThrough e C (n+1)) (e r) (B.flip (e r)) k)
--       (a : ℝ) (ha : a∈lineEvents (realRootsThrough e C (n+1)) (B.flip (e r)) k) :
--       ∃ε > 0,∀δ : ℝ,0 < δ → δ < ε →
--         RootClosedThrough LaurentRay.vUnit Ω (n+1) (literalRootProducts Ω C (OnPositiveRay r))
--           (chartZero LaurentRay.vUnit Ω C ((k+(a+δ) • B.flip (e r)).toAddMonoidHom.comp e) F).val →
--         RootClosedThrough LaurentRay.vUnit Ω (n+1) (literalRootProducts Ω C (OnPositiveRay r))
--           (chartZero LaurentRay.vUnit Ω C ((k+(a-δ) • B.flip (e r)).toAddMonoidHom.comp e) F).val
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.FiniteRayGeometry.GenericOffset`, `OAI.ElementaryPositivity.QuantumTorus.CompletedPositive`, `OAI.ElementaryPositivity.QuantumTorus.HasRootDegree`, `OAI.ElementaryPositivity.QuantumTorus.OnPositiveRay`, `OAI.ElementaryPositivity.QuantumTorus.Torus`, `OAI.ElementaryPositivity.QuantumTorus.chartCompletionAddGroup`, `OAI.ElementaryPositivity.QuantumTorus.chartZero`, `OAI.ElementaryPositivity.QuantumTorus.lineEvents`, `OAI.ElementaryPositivity.QuantumTorus.literalRootProducts`, `OAI.ElementaryPositivity.QuantumTorus.realRootsThrough`, `OAI.ElementaryPositivity.QuantumTorus.rootGrade`, `OAI.ElementaryPositivity.QuantumTorus.Torus.instOne`, `OAI.ElementaryPositivity.QuantumTorus.Torus.instRing` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.QuantumTorus.RootClosedThrough` and `OAI.ElementaryPositivity.QuantumTorus.WallsPositiveThrough` (definitions bundle `OAIQ368Chrom013` of this split).
--
--   **Used by.** The proofs of `OAI.ElementaryPositivity.QuantumTorus.polynomial_common_history` and `OAI.ElementaryPositivity.QuantumTorus.positive_sections` of this split import it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/PlanarRefinement.lean (declaration OAI.ElementaryPositivity.QuantumTorus.wall_joint_induction)

import Mathlib
import Definitions.Def_OAIQ368Chrom013

section

attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry RootTruncation WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (e : M →+ E)
variable (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in
theorem wall_joint_induction (n dr : ℕ) (r : M) (hdr : 0 < dr) (hrd : HasRootDegree C dr r)
    (F : CompletedPositive LaurentRay.vUnit Ω C) (ih : WallsPositiveThrough Ω C e n F)
    (k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C (n+1)) (e r) (B.flip (e r)) k)
    (a : ℝ) (ha : a∈lineEvents (realRootsThrough e C (n+1)) (B.flip (e r)) k) :
    ∃ε > 0,∀δ : ℝ,0 < δ → δ < ε →
      RootClosedThrough LaurentRay.vUnit Ω (n+1) (literalRootProducts Ω C (OnPositiveRay r))
        (chartZero LaurentRay.vUnit Ω C ((k+(a+δ) • B.flip (e r)).toAddMonoidHom.comp e) F).val →
      RootClosedThrough LaurentRay.vUnit Ω (n+1) (literalRootProducts Ω C (OnPositiveRay r))
        (chartZero LaurentRay.vUnit Ω C ((k+(a-δ) • B.flip (e r)).toAddMonoidHom.comp e) F).val := by
  sorry
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end
