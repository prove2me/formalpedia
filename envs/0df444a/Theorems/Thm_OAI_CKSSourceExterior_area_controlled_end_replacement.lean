-- Prove2me | Theorems.Thm_OAI_CKSSourceExterior_area_controlled_end_replacement
-- name    : OAI.CKSSourceExterior.area_controlled_end_replacement
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:25.678152+00:00
-- url     : https://prove2.me/theorems/ff8af108-cac1-4ae4-b92c-f7df3364caa0
-- statement:
--   The theorem states that, for a connected, Hausdorff, second countable smooth 3-manifold N with boundary and a smooth Riemannian metric g with a smooth symmetric tensor field K, such that N is orientable, the boundary is compact and nonempty, g is complete, and (g,K) satisfies the pointwise local-chart physical dominant energy condition PhysicalDEC, the following holds. Suppose d is a CKS exterior-end datum for (g,K): a coordinate end outside radius d.chart.radius in which g and K are represented by smooth perturbations, together with a smooth mass aspect function on the sphere and the tensor patches realizing it. If the Bondi charge (energy, momentum) of d's mass aspect, (E,P), is timelike, meaning |P|<E, then there exist another such datum d', a radius R₀ with d'.chart.radius<R₀ and 12≤R₀, and a function ε with ε(R)→0 as R→∞, such that d' has Bondi charge (√(E²−|P|²),0), and the minimal enclosing area of g is finite. Moreover, for every R≥R₀ one has 0≤ε(R)<1 and there are a complete smooth metric gR, a smooth symmetric tensor field kR, spatial tensor fields G and k on Euclidean 3-space, and a number η with these properties. The pair (gR,kR) agrees with (g,K) at every point outside the chart domain or with chart coordinate norm at most R, and satisfies PhysicalDEC and integrable constraints. Also gR≥(1−ε(R))g as quadratic forms. On the end, gR and kR equal the end metrics built from G and k in d'.chart. Each Cartesian component of G minus the identity satisfies the order-1 Symbol condition from CKSADM, and k vanishes where ‖x‖>2R². As r→∞ the spatial ADM energy of G tends to √(E²−|P|²)+η and the ADM momentum of (G,k) tends to 0, with 0≤η≤2R^(−1/2). Finally, gR has finite minimal enclosing area, (1−ε(R)) times the minimum enclosing area of g is at most that of gR, and for every outer domain D the cut areas of g and gR are finite and satisfy (1−ε(R))·cutArea(g,D)≤cutArea(gR,D).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CKSBondiPenrose.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CKSBondiPenrose.lean; bytes 176105..179638
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CKSBondiPenrose

noncomputable section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6

namespace OAI.CKSSourceExterior

open Set Manifold Bundle Filter CKSLorentz CKSMetricGluing CKSSpatialManifold CKSGeometricCuts

open CKSADM (Symbol)

open scoped ContDiff Topology

variable {N : Type u_1} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  [T2Space N] [SecondCountableTopology N] [ConnectedSpace N]

attribute [local instance] manifold_regular

theorem area_controlled_end_replacement
    (g : OAI.CKSMetricGluing.SmoothMetric OAI.CKSGeometricCuts.I3 (M := N)) (K : OAI.CKSMetricGluing.InnerField OAI.CKSGeometricCuts.I3 (M := N))
    (hK : ContMDiff OAI.CKSGeometricCuts.I3 (OAI.CKSGeometricCuts.I3.prod 𝓘(ℝ,OAI.CKSLorentz.SpatialBilinear)) ∞ (OAI.CKSMetricGluing.innerSection OAI.CKSGeometricCuts.I3 K))
    (hKsym : ∀ x v w, K x v w = K x w v)
    (hOrient : OAI.CKSSourceExterior.Orientable (N := N))
    (hScompact : IsCompact (OAI.CKSGeometricCuts.I3.boundary N)) (hSnonempty : (OAI.CKSGeometricCuts.I3.boundary N).Nonempty)
    (hcomplete : OAI.CKSReplacementCompleteness.IsComplete OAI.CKSGeometricCuts.I3 g.toContinuousRiemannianMetric)
    (hDEC : OAI.CKSSpatialManifold.PhysicalDEC OAI.CKSGeometricCuts.I3 g.inner K)
    (d : OAI.CKSSourceExterior.CKSData g K)
    (ht : ‖(OAI.CKSLorentz.bondiCharge d.massAspect).2‖ < (OAI.CKSLorentz.bondiCharge d.massAspect).1) :
    ∃ (d' : OAI.CKSSourceExterior.CKSData g K) (R₀ : ℝ) (ε : ℝ → ℝ),
      OAI.CKSLorentz.bondiCharge d'.massAspect =
        (Real.sqrt ((OAI.CKSLorentz.bondiCharge d.massAspect).1^2 - ‖(OAI.CKSLorentz.bondiCharge d.massAspect).2‖^2),0) ∧
      d'.chart.radius < R₀ ∧ 12 ≤ R₀ ∧ Tendsto ε atTop (𝓝 0) ∧
      OAI.CKSFullCutArea.minEnclosingArea g < ⊤ ∧
      ∀ R ≥ R₀, (0 ≤ ε R ∧ ε R < 1) ∧
        ∃ (gR : OAI.CKSMetricGluing.SmoothMetric OAI.CKSGeometricCuts.I3 (M := N)) (kR : OAI.CKSMetricGluing.InnerField OAI.CKSGeometricCuts.I3 (M := N))
          (G k : OAI.CKSLorentz.SpatialTensor) (η : ℝ),
          ContMDiff OAI.CKSGeometricCuts.I3 (OAI.CKSGeometricCuts.I3.prod 𝓘(ℝ,OAI.CKSLorentz.SpatialBilinear)) ∞ (OAI.CKSMetricGluing.innerSection OAI.CKSGeometricCuts.I3 kR) ∧
          (∀ x v w, kR x v w = kR x w v) ∧
          (∀ x, x ∉ d'.chart.domain ∨ ‖d'.chart.coordinate x‖ ≤ R →
            gR.inner x = g.inner x ∧ kR x = K x) ∧
          OAI.CKSSpatialManifold.PhysicalDEC OAI.CKSGeometricCuts.I3 gR.inner kR ∧
          (∀ x v, (1-ε R) * g.inner x v v ≤ gR.inner x v v) ∧
          OAI.CKSReplacementCompleteness.IsComplete OAI.CKSGeometricCuts.I3 gR.toContinuousRiemannianMetric ∧
          OAI.CKSSourceExterior.constraintsIntegrable gR kR ∧
          (∀ x ∈ d'.chart.domain,
            gR.inner x = OAI.CKSSpatialManifold.endInner OAI.CKSGeometricCuts.I3 d'.chart.coordinate G x ∧
            kR x = OAI.CKSSpatialManifold.endInner OAI.CKSGeometricCuts.I3 d'.chart.coordinate k x) ∧
          (∀ i j : Fin 3, OAI.CKSADM.Symbol 1
            (fun x => OAI.CKSLorentz.spatialCartesian G x i j - (if i=j then 1 else 0))) ∧
          (∀ x : OAI.CKSLorentz.E, 2*R^2 < ‖x‖ → k x = 0) ∧
          Tendsto (OAI.CKSLorentz.spatialADMEnergy G) atTop
            (𝓝 (Real.sqrt ((OAI.CKSLorentz.bondiCharge d.massAspect).1^2 - ‖(OAI.CKSLorentz.bondiCharge d.massAspect).2‖^2) + η)) ∧
          Tendsto (OAI.CKSLorentz.spatialADMMomentum G k) atTop (𝓝 0) ∧
          0 ≤ η ∧ η ≤ 2 * R ^ (-(1/2 : ℝ)) ∧
          OAI.CKSFullCutArea.minEnclosingArea gR < ⊤ ∧
          (1-ε R) * OAI.CKSSourceExterior.minimumEnclosingArea g ≤ OAI.CKSSourceExterior.minimumEnclosingArea gR ∧
          ∀ D : OAI.CKSGeometricCuts.OuterDomain N,
            OAI.CKSFullCutArea.area g D < ⊤ ∧ OAI.CKSFullCutArea.area gR D < ⊤ ∧
            (1-ε R) * OAI.CKSSourceExterior.cutArea g D ≤ OAI.CKSSourceExterior.cutArea gR D := by
  sorry

end OAI.CKSSourceExterior
end
