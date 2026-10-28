-- Prove2me | Theorems.Thm_K24_Global_originalSobolevCutoffMultipliers
-- name    : K24.Global.originalSobolevCutoffMultipliers
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-26T04:59:31.840862+00:00
-- url     : https://prove2.me/theorems/f859fe8c-2cb8-4e81-9b98-6f172d69b1af
-- title:
--   K24: uniform cutoff multipliers at all three original real Sobolev orders
-- statement:
--   For every real $s>4$, integer $m\ge s+2$, and outer-chart radius $R$, there is a finite constant $K=K(s,m,R)$, chosen before the manifold, bounded cover, partition, localizers, derivative bound, chart, and function. If the original partition cutoffs and collar localizers have derivatives through order $m$ bounded by $B$, then for every $j\in\{0,1,2\}$ and $f\in H^{s-j}(\mathbb R^4)$, both actual partition localization and multiplication by an original collar cutoff remain in the same original Bessel Sobolev class and satisfy $$\|P_\nu f\|_{H^{s-j}},\ \|L_\nu f\|_{H^{s-j}}\le KB\|f\|_{H^{s-j}}.$$ The norms and cutoffs are exactly those of the fixed K24 model. The endpoint $m=s+2$, when integral, is included. This supplies the same-chart multiplier estimates needed at the source, intermediate, and target levels of the original Sobolev analytic core. Coordinate transitions and global gluing remain separate obligations.
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — derived same-chart localization foundation at all three original real Sobolev orders in §3. Original canonical cutoffs, collar localizers, derivative budget, and Bessel norms are retained.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
universe u
noncomputable section
open scoped NNReal ENNReal Topology Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 16

open K24.Global

theorem K24.Global.originalSobolevCutoffMultipliers :
∀ (s : ℝ), 4 < s → ∀ m : ℕ, s + 2 ≤ (m : ℝ) → ∀ R : ℝ,
    ∃ K : ℝ≥0,
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
        (C : BoundedLocalCover M), C.numerics.outerRadius = R →
        ∀ (P : SobolevPartition C) (L : SobolevLocalizers C) (B : ℝ≥0),
          P.CutoffDerivativeBounds m B → L.DerivativeBounds m B →
          ∀ j : ℕ, j ≤ 2 →
            ∀ (ν : C.Index) (f : SobolevModel → ℝ), LocalSobolevMem (s - j) f →
              (LocalSobolevMem (s - j) (P.localize ν f) ∧
                localSobolevENN (s - j) (P.localize ν f) ≤
                  (K : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN (s - j) f) ∧
              (LocalSobolevMem (s - j) (L.cutoff ν * f) ∧
                localSobolevENN (s - j) (L.cutoff ν * f) ≤
                  (K : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN (s - j) f) := by sorry
