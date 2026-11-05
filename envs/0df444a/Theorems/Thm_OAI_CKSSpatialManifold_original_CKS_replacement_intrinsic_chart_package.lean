-- Prove2me | Theorems.Thm_OAI_CKSSpatialManifold_original_CKS_replacement_intrinsic_chart_package
-- name    : OAI.CKSSpatialManifold.original_CKS_replacement_intrinsic_chart_package
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:39:55.392031+00:00
-- url     : https://prove2.me/theorems/cf62ddaf-ffce-4ca5-b609-618e98a8c9ec
-- title:
--   The intrinsic replacement package with its boosted end chart
-- statement:
--   Let $M$ be a smooth mass aspect with Bondi charge $(e,p)$, $\|p\|<e$, let $(N,g,K)$ be a complete three-manifold with boundary satisfying the physical DEC, and let $f$ be an end chart on an open set $U$ representing $g,K$ as `sourceSpatial A`, `sourceSpatial B`, with the CKS patch and regularity hypotheses for $(A,B)$. Let $C\subset N$ be compact. With $H$ the boost homeomorphism and $f'=H^{-1}\circ f$, there are $T,R_0$ with $0<T<R_0$, $12\le R_0$, $\varepsilon$ with $\varepsilon(R)\to 0$, and families $G,k$ of spatial tensors such that $f'$ is an end chart above radius $T$, and for each $R\ge R_0$ we have $0\le\varepsilon(R)<1$ and there is smooth data $(g',K')$ on $N$ with: symmetric $K'$, the physical DEC, completeness, agreement with $(g,K)$ on $C$ and on the side $\|f'\|\le R$ of the chart, the metric lower bound with $\varepsilon(R)$, the enclosing-area inequality, representation by $G(R),k(R)$ in $f'$, vanishing of $k(R)$ beyond $2R^2$, symbol-order decay of $G(R)-\delta$, ADM energy limit $\sqrt{e^2-\|p\|^2}+\eta_R$, ADM momentum limit $0$, $0\le\eta_R\le 2/\sqrt R$, integrability of the constraints on the end, vanishing momentum beyond $2R^2$, the global integrability `IntegrableConstraints g' K'`, and, for every outer domain $D$, finiteness of the areas of $D$ for $g$ and $g'$ with $(1-\varepsilon(R))\,\mathrm{Area}_g(D)\le\mathrm{Area}_{g'}(D)$.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem original_CKS_replacement_intrinsic_chart_package
--       {M : CKSLorentz.Sphere → ℝ} (hM : SmoothSphere M)
--       (ht : ‖(bondiCharge M).2‖ < (bondiCharge M).1)
--       (A B : SpatialTensor) (old : CKSLorentz.Sphere → CKSTensorPatch)
--       (hold : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
--       (hrep : ∀ n, (old n).RepresentsMassAspect M)
--       (hreal : ∀ n, (old n).Realizes A B)
--       {S : ℝ} (hS : 0 < S)
--       (hAs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ A x)
--       (hBs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ B x)
--       (hA : ∀ x, S < ‖x‖ → ∀ v w, A x v w = A x w v)
--       (hB : ∀ x, S < ‖x‖ → ∀ v w, B x v w = B x w v)
--       (hpos : ∀ x, S < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < sourceSpatial A x v v)
--       (hDEC : ∀ x, S < ‖x‖ → spatialDEC (sourceSpatial A) (sourceSpatial B) x)
--       (g : SmoothMetric I3 (M := N)) (K : InnerField I3 (M := N))
--       (hK : ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 K))
--       (hKsym : ∀ x v w, K x v w = K x w v)
--       (hgDEC : PhysicalDEC I3 g.inner K)
--       (hgcomplete : CKSReplacementCompleteness.IsComplete I3 g.toContinuousRiemannianMetric)
--       (f : N → E) {U : Set N} (hU : IsOpen U)
--       (hf : ContMDiffOn I3 𝓘(ℝ,E) ∞ f U)
--       (hclosed : ∀ r, S < r → IsClosed {x : N | x ∈ U ∧ r ≤ ‖f x‖})
--       (finv : E → N)
--       (hi : ContMDiffOn 𝓘(ℝ,E) I3 ∞ finv {y | S < ‖y‖})
--       (hleft : ∀ x ∈ U, finv (f x) = x)
--       (hright : ∀ y, S < ‖y‖ → finv y ∈ U ∧ f (finv y) = y)
--       (hcompact : ∀ r, S < r → IsCompact {x : N | x ∉ U ∨ ‖f x‖ ≤ r})
--       (hsource : ∀ x ∈ U, g.inner x = endInner I3 f (sourceSpatial A) x ∧
--         K x = endInner I3 f (sourceSpatial B) x)
--       {C : Set N} (hC : IsCompact C) :
--       let e := (bondiCharge M).1
--       let p := (bondiCharge M).2
--       let H := hyperbolicHomeomorph e p ht
--       let f' := H.symm ∘ f
--       let inv' := finv ∘ H
--       ∃ (T R₀ : ℝ) (ε : ℝ → ℝ) (G k : ℝ → SpatialTensor),
--         0 < T ∧ T < R₀ ∧ 12 ≤ R₀ ∧ Tendsto ε atTop (𝓝 0) ∧
--         let V := {x : N | x ∈ U ∧ T < ‖f' x‖}
--         IsOpen V ∧ ContMDiffOn I3 𝓘(ℝ,E) ∞ f' V ∧
--         ContMDiffOn 𝓘(ℝ,E) I3 ∞ inv' {y | T < ‖y‖} ∧
--         (∀ x ∈ V, inv' (f' x) = x) ∧
--         (∀ y, T < ‖y‖ → inv' y ∈ V ∧ f' (inv' y) = y) ∧
--         (∀ r, T < r → IsClosed {x : N | x ∈ V ∧ r ≤ ‖f' x‖}) ∧
--         (∀ r, T ≤ r → IsCompact {x : N | x ∉ V ∨ ‖f' x‖ ≤ r}) ∧
--         ∀ R ≥ R₀, (0 ≤ ε R ∧ ε R < 1) ∧
--           ∃ (g' : SmoothMetric I3 (M := N)) (K' : InnerField I3 (M := N)),
--             ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 K') ∧
--             (∀ x v w, K' x v w = K' x w v) ∧
--             PhysicalDEC I3 g'.inner K' ∧
--             CKSReplacementCompleteness.IsComplete I3 g'.toContinuousRiemannianMetric ∧
--             (∀ x ∈ C, g'.inner x = g.inner x ∧ K' x = K x) ∧
--             (∀ x, x ∉ V ∨ ‖f' x‖ ≤ R → g'.inner x = g.inner x ∧ K' x = K x) ∧
--             CKSReplacementCompleteness.MetricLower I3 g.toContinuousRiemannianMetric g'.toContinuousRiemannianMetric (ε R) ∧
--             ENNReal.ofReal (1-ε R)*minEnclosingArea N g.toContinuousRiemannianMetric ≤
--               minEnclosingArea N g'.toContinuousRiemannianMetric ∧
--             (∀ x, x ∈ U ∧ T < ‖f' x‖ →
--               g'.inner x = endInner I3 f' (G R) x ∧ K' x = endInner I3 f' (k R) x) ∧
--             (∀ x : E, 2*R^2 < ‖x‖ → k R x = 0) ∧
--             (∀ i j : Fin 3, Symbol 1 (fun x => spatialCartesian (G R) x i j - (if i=j then 1 else 0))) ∧
--             Tendsto (spatialADMEnergy (G R)) atTop (𝓝 (mass e p + paddingCharge R)) ∧
--             Tendsto (spatialADMMomentum (G R) (k R)) atTop (𝓝 0) ∧
--             0 ≤ paddingCharge R ∧ paddingCharge R ≤ 2/Real.sqrt R ∧
--             (∀ s : ℝ, T < s →
--               IntegrableOn (spatialEnergy (G R) (k R)) (CKSTailVolume.tailRegion s) (spatialVolume (G R)) ∧
--               IntegrableOn (fun x => Real.sqrt (CKSLocalBending.momentumSq
--                 (CKSAngularGeometry.physicalMetricJet (spatialCoefficients (G R)) (CKSCartesianOuter.toPoint x))
--                 (CKSAngularGeometry.physicalTensorJet (spatialCoefficients (k R)) (CKSCartesianOuter.toPoint x))))
--                 (CKSTailVolume.tailRegion s) (spatialVolume (G R))) ∧
--             (∀ x : E, 2*R^2 < ‖x‖ → spatialMomentum (G R) (k R) x = 0) ∧
--             CKSIntrinsicConstraints.IntegrableConstraints g' K' ∧
--             ENNReal.ofReal (1-ε R) * CKSFullCutArea.minEnclosingArea g ≤
--               CKSFullCutArea.minEnclosingArea g' ∧
--             ∀ D : OuterDomain N,
--               CKSFullCutArea.area g D < ⊤ ∧ CKSFullCutArea.area g' D < ⊤ ∧
--               ENNReal.ofReal (1-ε R) * CKSFullCutArea.area g D ≤ CKSFullCutArea.area g' D
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/IntrinsicReplacementWithChart.lean`, lines 16-159, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/IntrinsicReplacementWithChart.lean#L16-L159 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

namespace OAI

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter MeasureTheory CKSLorentz CKSMetricGluing CKSGeometricCuts
open CKSSphericalHarmonics CKSADM CKSBending
open scoped Bundle Manifold ContDiff Topology
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N] [T3Space N]
  [MeasurableSpace N] [BorelSpace N] [SecondCountableTopology N]

theorem original_CKS_replacement_intrinsic_chart_package
    {M : CKSLorentz.Sphere → ℝ} (hM : SmoothSphere M)
    (ht : ‖(bondiCharge M).2‖ < (bondiCharge M).1)
    (A B : SpatialTensor) (old : CKSLorentz.Sphere → CKSTensorPatch)
    (hold : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
    (hrep : ∀ n, (old n).RepresentsMassAspect M)
    (hreal : ∀ n, (old n).Realizes A B)
    {S : ℝ} (hS : 0 < S)
    (hAs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ A x)
    (hBs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ B x)
    (hA : ∀ x, S < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, S < ‖x‖ → ∀ v w, B x v w = B x w v)
    (hpos : ∀ x, S < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < sourceSpatial A x v v)
    (hDEC : ∀ x, S < ‖x‖ → spatialDEC (sourceSpatial A) (sourceSpatial B) x)
    (g : SmoothMetric I3 (M := N)) (K : InnerField I3 (M := N))
    (hK : ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 K))
    (hKsym : ∀ x v w, K x v w = K x w v)
    (hgDEC : PhysicalDEC I3 g.inner K)
    (hgcomplete : CKSReplacementCompleteness.IsComplete I3 g.toContinuousRiemannianMetric)
    (f : N → E) {U : Set N} (hU : IsOpen U)
    (hf : ContMDiffOn I3 𝓘(ℝ,E) ∞ f U)
    (hclosed : ∀ r, S < r → IsClosed {x : N | x ∈ U ∧ r ≤ ‖f x‖})
    (finv : E → N)
    (hi : ContMDiffOn 𝓘(ℝ,E) I3 ∞ finv {y | S < ‖y‖})
    (hleft : ∀ x ∈ U, finv (f x) = x)
    (hright : ∀ y, S < ‖y‖ → finv y ∈ U ∧ f (finv y) = y)
    (hcompact : ∀ r, S < r → IsCompact {x : N | x ∉ U ∨ ‖f x‖ ≤ r})
    (hsource : ∀ x ∈ U, g.inner x = endInner I3 f (sourceSpatial A) x ∧
      K x = endInner I3 f (sourceSpatial B) x)
    {C : Set N} (hC : IsCompact C) :
    let e := (bondiCharge M).1
    let p := (bondiCharge M).2
    let H := hyperbolicHomeomorph e p ht
    let f' := H.symm ∘ f
    let inv' := finv ∘ H
    ∃ (T R₀ : ℝ) (ε : ℝ → ℝ) (G k : ℝ → SpatialTensor),
      0 < T ∧ T < R₀ ∧ 12 ≤ R₀ ∧ Tendsto ε atTop (𝓝 0) ∧
      let V := {x : N | x ∈ U ∧ T < ‖f' x‖}
      IsOpen V ∧ ContMDiffOn I3 𝓘(ℝ,E) ∞ f' V ∧
      ContMDiffOn 𝓘(ℝ,E) I3 ∞ inv' {y | T < ‖y‖} ∧
      (∀ x ∈ V, inv' (f' x) = x) ∧
      (∀ y, T < ‖y‖ → inv' y ∈ V ∧ f' (inv' y) = y) ∧
      (∀ r, T < r → IsClosed {x : N | x ∈ V ∧ r ≤ ‖f' x‖}) ∧
      (∀ r, T ≤ r → IsCompact {x : N | x ∉ V ∨ ‖f' x‖ ≤ r}) ∧
      ∀ R ≥ R₀, (0 ≤ ε R ∧ ε R < 1) ∧
        ∃ (g' : SmoothMetric I3 (M := N)) (K' : InnerField I3 (M := N)),
          ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 K') ∧
          (∀ x v w, K' x v w = K' x w v) ∧
          PhysicalDEC I3 g'.inner K' ∧
          CKSReplacementCompleteness.IsComplete I3 g'.toContinuousRiemannianMetric ∧
          (∀ x ∈ C, g'.inner x = g.inner x ∧ K' x = K x) ∧
          (∀ x, x ∉ V ∨ ‖f' x‖ ≤ R → g'.inner x = g.inner x ∧ K' x = K x) ∧
          CKSReplacementCompleteness.MetricLower I3 g.toContinuousRiemannianMetric g'.toContinuousRiemannianMetric (ε R) ∧
          ENNReal.ofReal (1-ε R)*minEnclosingArea N g.toContinuousRiemannianMetric ≤
            minEnclosingArea N g'.toContinuousRiemannianMetric ∧
          (∀ x, x ∈ U ∧ T < ‖f' x‖ →
            g'.inner x = endInner I3 f' (G R) x ∧ K' x = endInner I3 f' (k R) x) ∧
          (∀ x : E, 2*R^2 < ‖x‖ → k R x = 0) ∧
          (∀ i j : Fin 3, Symbol 1 (fun x => spatialCartesian (G R) x i j - (if i=j then 1 else 0))) ∧
          Tendsto (spatialADMEnergy (G R)) atTop (𝓝 (mass e p + paddingCharge R)) ∧
          Tendsto (spatialADMMomentum (G R) (k R)) atTop (𝓝 0) ∧
          0 ≤ paddingCharge R ∧ paddingCharge R ≤ 2/Real.sqrt R ∧
          (∀ s : ℝ, T < s →
            IntegrableOn (spatialEnergy (G R) (k R)) (CKSTailVolume.tailRegion s) (spatialVolume (G R)) ∧
            IntegrableOn (fun x => Real.sqrt (CKSLocalBending.momentumSq
              (CKSAngularGeometry.physicalMetricJet (spatialCoefficients (G R)) (CKSCartesianOuter.toPoint x))
              (CKSAngularGeometry.physicalTensorJet (spatialCoefficients (k R)) (CKSCartesianOuter.toPoint x))))
              (CKSTailVolume.tailRegion s) (spatialVolume (G R))) ∧
          (∀ x : E, 2*R^2 < ‖x‖ → spatialMomentum (G R) (k R) x = 0) ∧
          CKSIntrinsicConstraints.IntegrableConstraints g' K' ∧
          ENNReal.ofReal (1-ε R) * CKSFullCutArea.minEnclosingArea g ≤
            CKSFullCutArea.minEnclosingArea g' ∧
          ∀ D : OuterDomain N,
            CKSFullCutArea.area g D < ⊤ ∧ CKSFullCutArea.area g' D < ⊤ ∧
            ENNReal.ofReal (1-ε R) * CKSFullCutArea.area g D ≤ CKSFullCutArea.area g' D := by
  sorry

end
end CKSSpatialManifold
end
end OAI
