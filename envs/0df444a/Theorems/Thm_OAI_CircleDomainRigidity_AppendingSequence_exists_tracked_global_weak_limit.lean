-- Prove2me | Theorems.Thm_OAI_CircleDomainRigidity_AppendingSequence_exists_tracked_global_weak_limit
-- name    : OAI.CircleDomainRigidity.AppendingSequence.exists_tracked_global_weak_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T05:24:35.643878+00:00
-- url     : https://prove2.me/theorems/44a19ccd-7665-4642-a9a4-9682a843f677
-- title:
--   OAI.CircleDomainRigidity.AppendingSequence.exists_tracked_global_weak_limit: intermediate lemma from OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleDomainRigidity.AppendingSequence.exists_tracked_global_weak_limit` of [lean/OAI/Analysis/CircleDomains/Sobolev/TrackedGlobalWeakLimit.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Sobolev/TrackedGlobalWeakLimit.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleDomainRigidity.AppendingSequence`, with `open Set Function Filter MeasureTheory`, `open scoped Topology ENNReal`):
--
--   ```lean
--    theorem exists_tracked_global_weak_limit
--       (hprincipal : PrincipalRealBeltrami) (harea : ExteriorCoefficientAreaTheorem)
--       (hconn : IsConnected G) (hrem : IsConformallyRemovable Gᶜ)
--       (M : ∀ n, CompactScalarCircleModel G (states n).family.test)
--       {σ : ℕ → ℕ} (hσ : StrictMono σ) {F : ℂ → ℂ}
--       (hnorm : IsPrincipalNormalized (extendAtInfinity F))
--       (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
--       (hlim : TendstoLocallyUniformlyOn (fun n => (M (σ n)).function) F atTop
--         {z : ℂ | (z : Sphere) ∈ G}) (i : Fin T.count) :
--       ∃ (v : C(Sphere,ℝ)) (g : EuclideanPlane → EuclideanPlane),
--         (∀ p, |v p-sphereFromPlaneFunction (T.test i) p| ≤ ε/4) ∧
--         MemLp g 2 volume ∧ DeGiorgi.HasWeakGrad g (fun x => v (planeSphere x)) univ ∧
--         (∫ x, ‖g x‖^2) ≤
--           (‖(T.witness i).weakGrad_memLp.toLp ((T.witness i).weakGrad)‖+ε/4)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CircleDomainRigidity.EuclideanPlane`, `OAI.CircleDomainRigidity.FiniteCompactTests`, `OAI.CircleDomainRigidity.PlanarSchoenflies`, `OAI.CircleDomainRigidity.SmoothPlanarSard`, `OAI.CircleDomainRigidity.extendAtInfinity`, `OAI.CircleDomainRigidity.physicalPlaneDomain`, `OAI.CircleDomainRigidity.planeSphere`, `OAI.CircleDomainRigidity.sphereFromPlaneFunction`, `OAI.DeGiorgi.HasWeakGrad`, `OAI.CircleDomainRigidity.AppendingConstructionState`, `OAI.DeGiorgi.MemW1pWitness` and `OAI.DeGiorgi.MemW1pWitness.weakGrad_memLp` (definitions bundle `Q146C001` of this split); `OAI.CircleDomainRigidity.ExteriorCoefficientAreaTheorem` (definitions bundle `Q146C002` of this split); `OAI.CircleDomainRigidity.CompactScalarCircleModel`, `OAI.CircleDomainRigidity.FiniteAppendingSupply` and `OAI.CircleDomainRigidity.IsPrincipalNormalized` (definitions bundle `Q146C004` of this split); `OAI.CircleDomainRigidity.PrincipalRealBeltrami` (definitions bundle `Q146C005` of this split); `OAI.CircleDomainRigidity.appendingStates` (definitions bundle `Q146C007` of this split); `OAI.CircleDomainRigidity.IsConformalEquivalence`, `OAI.CircleDomainRigidity.IsConformallyRemovable` and `OAI.CircleDomainRigidity.Sphere` (the published bundle `Def_KoebeCircleDomains`).
--
--   **Used by.** The proof of `OAI.CircleDomainRigidity.MatchedConformalEnds.MatchedRealMask.global_sobolev_of_published_inputs` of this split imports it.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Sobolev/TrackedGlobalWeakLimit.lean (declaration OAI.CircleDomainRigidity.AppendingSequence.exists_tracked_global_weak_limit)

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C007

section

attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "f" => scalar hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "W" => witness hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "idx" => index hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "sf" => sphereScalar hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem exists_tracked_global_weak_limit
    (hprincipal : PrincipalRealBeltrami) (harea : ExteriorCoefficientAreaTheorem)
    (hconn : IsConnected G) (hrem : IsConformallyRemovable Gᶜ)
    (M : ∀ n, CompactScalarCircleModel G (states n).family.test)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {F : ℂ → ℂ}
    (hnorm : IsPrincipalNormalized (extendAtInfinity F))
    (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
    (hlim : TendstoLocallyUniformlyOn (fun n => (M (σ n)).function) F atTop
      {z : ℂ | (z : Sphere) ∈ G}) (i : Fin T.count) :
    ∃ (v : C(Sphere,ℝ)) (g : EuclideanPlane → EuclideanPlane),
      (∀ p, |v p-sphereFromPlaneFunction (T.test i) p| ≤ ε/4) ∧
      MemLp g 2 volume ∧ DeGiorgi.HasWeakGrad g (fun x => v (planeSphere x)) univ ∧
      (∫ x, ‖g x‖^2) ≤
        (‖(T.witness i).weakGrad_memLp.toLp ((T.witness i).weakGrad)‖+ε/4)^2 := by
  sorry

end AppendingSequence
end CircleDomainRigidity

end

end OAI
end
