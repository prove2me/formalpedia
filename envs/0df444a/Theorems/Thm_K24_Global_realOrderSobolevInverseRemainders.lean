-- Prove2me | Theorems.Thm_K24_Global_realOrderSobolevInverseRemainders
-- name    : K24.Global.realOrderSobolevInverseRemainders
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-26T04:50:41.424012+00:00
-- url     : https://prove2.me/theorems/1178d0fc-5935-4b74-b4e4-0b5105cde005
-- title:
--   K24: actual scalar and matrix inverse remainders in real-order Sobolev norms
-- statement:
--   For every real r>2, sufficiently small continuous scalar perturbations u in the original local H^r norm have actual pointwise inverse differences (1+u)^(-1)-1 in that same Sobolev class, with norm at most twice the perturbation norm and an original-norm quadratic bound for the remainder (1+u)^(-1)-1+u. The same statement holds for actual 4 by 4 real matrix functions, with the unchanged matrixSobolevENN square-sum norm, actual determinant nonvanishing, actual matrix inverse, and entrywise continuous H^r representatives. Thresholds and finite remainder constants are chosen before the perturbation and depend only on r. No identity/constant function is asserted to belong to L2 on R4. The proof constructs the complete continuous Sobolev carrier with the exact original norm and applies a genuine contraction v -> -u-u*v. Its fixed-point identity proves pointwise invertibility and identifies v with the actual inverse difference; v+u=-u*v gives the quadratic bound. This is derived inverse-coefficient analytic infrastructure for the original Sobolev branch. It does not assert the global manifold partialGauge Frechet field or close the uniform analytic core. Parent https://prove2.me/theorems/06fdeaf7-3709-47fc-b5c6-674da98954a4 .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — derived local inverse-coefficient foundations for §3 equation (3.9) and §4; exact unchanged scalar and matrix Sobolev norms of K24GlobalAnalysis and K24GlobalStatement.

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

theorem K24.Global.realOrderSobolevInverseRemainders :
  (  ∀ (r : ℝ), 2 < r → ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0,
    ∀ u : K24.Global.SobolevModel → ℝ,
      Continuous u → K24.Global.LocalSobolevMem r u →
      K24.Global.localSobolevENN r u < ENNReal.ofReal δ →
      (∀ x, 1 + u x ≠ 0) ∧
      Continuous (fun x => (1 + u x)⁻¹ - 1) ∧
      K24.Global.LocalSobolevMem r (fun x => (1 + u x)⁻¹ - 1) ∧
      K24.Global.localSobolevENN r (fun x => (1 + u x)⁻¹ - 1) ≤
        2 * K24.Global.localSobolevENN r u ∧
      Continuous (fun x => (1 + u x)⁻¹ - 1 + u x) ∧
      K24.Global.LocalSobolevMem r (fun x => (1 + u x)⁻¹ - 1 + u x) ∧
      K24.Global.localSobolevENN r (fun x => (1 + u x)⁻¹ - 1 + u x) ≤
        (C : ℝ≥0∞) * K24.Global.localSobolevENN r u ^ (2 : ℕ)) ∧
  (  ∀ (r : ℝ), 2 < r → ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0,
    ∀ u : K24.Global.FourSpace → K24.Global.Mat4,
      (∀ i j, Continuous (fun x => u x i j) ∧
        K24.Global.LocalSobolevMem r (fun x => u x i j)) →
      K24.Global.matrixSobolevENN r u < ENNReal.ofReal δ →
      (∀ x, (1 + u x).det ≠ 0) ∧
      Continuous (fun x => (1 + u x)⁻¹ - 1) ∧
      (∀ i j, Continuous (fun x => ((1 + u x)⁻¹ - 1) i j) ∧
        K24.Global.LocalSobolevMem r (fun x => ((1 + u x)⁻¹ - 1) i j)) ∧
      K24.Global.matrixSobolevENN r (fun x => (1 + u x)⁻¹ - 1) ≤
        2 * K24.Global.matrixSobolevENN r u ∧
      Continuous (fun x => (1 + u x)⁻¹ - 1 + u x) ∧
      (∀ i j, Continuous (fun x => ((1 + u x)⁻¹ - 1 + u x) i j) ∧
        K24.Global.LocalSobolevMem r (fun x => ((1 + u x)⁻¹ - 1 + u x) i j)) ∧
      K24.Global.matrixSobolevENN r (fun x => (1 + u x)⁻¹ - 1 + u x) ≤
        (C : ℝ≥0∞) * K24.Global.matrixSobolevENN r u ^ (2 : ℕ)) := by sorry
