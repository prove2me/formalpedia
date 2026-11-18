-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_mutatedIncoming_probe
-- name    : OAI.ElementaryPositivity.QuantumTorus.mutatedIncoming_probe
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:19:30.562484+00:00
-- url     : https://prove2.me/theorems/e298a4ac-a6f2-4142-80cf-e2dd945c260f
-- title:
--   OAI.ElementaryPositivity.QuantumTorus.mutatedIncoming_probe: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.QuantumTorus.mutatedIncoming_probe` of [lean/OAI/Combinatorics/Chromatic/Walls/MutationLogCompletion.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/MutationLogCompletion.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.QuantumTorus`, with `open PowerSeries WallUnits`):
--
--   ```lean
--   lemma mutatedIncoming_probe (pos : Bool) (d N : ℕ) (hdN : d≤N) (r : M)
--       {a b x y : Module.Dual ℝ E}
--       (HA : RegularCovector C e a) (HB : RegularCovector C e b)
--       (HX : RegularCovector C e x) (HY : RegularCovector C e y)
--       (hA : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
--         0 < realMutationCovector e S (simpleRoot C pc) a (e m))
--       (hB : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
--         realMutationCovector e S (simpleRoot C pc) b (e m)<0)
--       (hx : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
--         realMutationCovector e S (simpleRoot C pc) x (e m)≠0)
--       (hy : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
--         realMutationCovector e S (simpleRoot C pc) y (e m)≠0)
--       (hsx : cutSide pos (x.toAddMonoidHom.comp e) (simpleRoot C pc))
--       (hsy : cutSide pos (y.toAddMonoidHom.comp e) (simpleRoot C pc))
--       (hxo : ∀n≤(mutationSize Ω C pc+1)*d,∀m,HasRootDegree C n m →
--         (0 < incomingCovector Ω r m → 0<x (e m)) ∧ (incomingCovector Ω r m<0 → x (e m)<0))
--       (hyo : ∀n≤(mutationSize Ω C pc+1)*d,∀m,HasRootDegree C n m →
--         (0 < incomingCovector Ω r m → 0<y (e m)) ∧ (incomingCovector Ω r m<0 → y (e m)<0))
--       (hxn : ∀n≤N,∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
--         (0 < incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m →
--           0 < realMutationCovector e S (simpleRoot C pc) x (e m)) ∧
--         (incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m<0 →
--           realMutationCovector e S (simpleRoot C pc) x (e m)<0))
--       (hyn : ∀n≤N,∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
--         (0 < incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m →
--           0 < realMutationCovector e S (simpleRoot C pc) y (e m)) ∧
--         (incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m<0 →
--           realMutationCovector e S (simpleRoot C pc) y (e m)<0))
--       (hxr : 0≤x (e r)) (hyr : y (e r)<0) :
--       coeff d (FormalLog.log (chartZero LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
--         (incomingCovector Ω (mutationLinearPiece Ω C pc pos r))
--         (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val)
--           (mutationLinearPiece Ω C pc pos r)=
--         if d=(mutationNewOrder Ω C coord pc pos r).toNat then
--           ∑n∈Finset.range ((mutationSize Ω C pc+1)*d+1),
--             coeff n (FormalLog.log (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω r)
--               (simpleTotalTransport Ω C)).val) r else 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.FormalLog.log`, `OAI.ElementaryPositivity.QuantumTorus.HasRootDegree`, `OAI.ElementaryPositivity.QuantumTorus.RegularCovector`, `OAI.ElementaryPositivity.QuantumTorus.Torus`, `OAI.ElementaryPositivity.QuantumTorus.chartCompletionAddGroup`, `OAI.ElementaryPositivity.QuantumTorus.chartZero`, `OAI.ElementaryPositivity.QuantumTorus.cutSide`, `OAI.ElementaryPositivity.QuantumTorus.incomingCovector`, `OAI.ElementaryPositivity.QuantumTorus.mutatedRoots`, `OAI.ElementaryPositivity.QuantumTorus.mutationSize`, `OAI.ElementaryPositivity.QuantumTorus.rootGrade`, `OAI.ElementaryPositivity.QuantumTorus.simpleRoot`, `OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra`, `OAI.ElementaryPositivity.QuantumTorus.Torus.instOne`, `OAI.ElementaryPositivity.QuantumTorus.Torus.instRing` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.QuantumTorus.realMutationCovector` (definitions bundle `OAIQ368Chrom002` of this split); `OAI.ElementaryPositivity.QuantumTorus.mutationLinearPiece` and `OAI.ElementaryPositivity.QuantumTorus.mutationNewOrder` (definitions bundle `OAIQ368Chrom003` of this split); `OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_10` (definitions bundle `OAIQ368Chrom006` of this split); `OAI.ElementaryPositivity.QuantumTorus.mutatedTransport` and `OAI.ElementaryPositivity.QuantumTorus.simpleTotalTransport` (definitions bundle `OAIQ368Chrom008` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_canonical` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/MutationLogCompletion.lean (declaration OAI.ElementaryPositivity.QuantumTorus.mutatedIncoming_probe)

import Mathlib
import Definitions.Def_OAIQ368Chrom008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd : ∀r≠0,∃m,Ω r m≠0)
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_10
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_13_rbbe8d2_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_13_rbbe8d2_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hnd in
lemma mutatedIncoming_probe (pos : Bool) (d N : ℕ) (hdN : d≤N) (r : M)
    {a b x y : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (HX : RegularCovector C e x) (HY : RegularCovector C e y)
    (hA : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      0 < realMutationCovector e S (simpleRoot C pc) a (e m))
    (hB : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) b (e m)<0)
    (hx : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) x (e m)≠0)
    (hy : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) y (e m)≠0)
    (hsx : cutSide pos (x.toAddMonoidHom.comp e) (simpleRoot C pc))
    (hsy : cutSide pos (y.toAddMonoidHom.comp e) (simpleRoot C pc))
    (hxo : ∀n≤(mutationSize Ω C pc+1)*d,∀m,HasRootDegree C n m →
      (0 < incomingCovector Ω r m → 0<x (e m)) ∧ (incomingCovector Ω r m<0 → x (e m)<0))
    (hyo : ∀n≤(mutationSize Ω C pc+1)*d,∀m,HasRootDegree C n m →
      (0 < incomingCovector Ω r m → 0<y (e m)) ∧ (incomingCovector Ω r m<0 → y (e m)<0))
    (hxn : ∀n≤N,∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      (0 < incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m →
        0 < realMutationCovector e S (simpleRoot C pc) x (e m)) ∧
      (incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m<0 →
        realMutationCovector e S (simpleRoot C pc) x (e m)<0))
    (hyn : ∀n≤N,∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      (0 < incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m →
        0 < realMutationCovector e S (simpleRoot C pc) y (e m)) ∧
      (incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m<0 →
        realMutationCovector e S (simpleRoot C pc) y (e m)<0))
    (hxr : 0≤x (e r)) (hyr : y (e r)<0) :
    coeff d (FormalLog.log (chartZero LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (incomingCovector Ω (mutationLinearPiece Ω C pc pos r))
      (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val)
        (mutationLinearPiece Ω C pc pos r)=
      if d=(mutationNewOrder Ω C coord pc pos r).toNat then
        ∑n∈Finset.range ((mutationSize Ω C pc+1)*d+1),
          coeff n (FormalLog.log (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω r)
            (simpleTotalTransport Ω C)).val) r else 0 := by
  sorry
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end
