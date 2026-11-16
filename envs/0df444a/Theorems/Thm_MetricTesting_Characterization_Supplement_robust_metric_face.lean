-- Prove2me | Theorems.Thm_MetricTesting_Characterization_Supplement_robust_metric_face
-- name    : MetricTesting.Characterization.Supplement.robust_metric_face
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:22:09.417302+00:00
-- url     : https://prove2.me/theorems/61d4f7b4-76e9-4d88-9b42-c782d9f566b1
-- title:
--   Lemma 4.10 — Rational robust metric face
-- statement:
--   Fix a real $C>2$. There exist a rational $C_0$ satisfying $2<C_0<\min\{C,3\}$, a positive integer bit constant $B_C$, and a threshold $N_C$, such that every $n\ge N_C$ admits a rational metric array $A$ in $[1,C_0]$ and an edge-disjoint family $H$ of triangles with
--
--   $$|H|\ge n^2/20.$$
--
--   Each selected triangle has one designated tight triangle inequality, and these are exactly all tight inequalities of $A$. Every other triangle inequality has slack at least $n^{-3}$, and every entry lies at least $n^{-3}$ from both endpoints of $[1,C_0]$. Every reduced rational entry has numerator and denominator bit lengths at most $B_C(1+\lceil\log_2 n\rceil)$.
--
--   The robust face provides the numerical margins and dense edge-disjoint tight family used by the packing obstruction. The witnesses and bit constant are uniform over orders above the threshold.
--
--   Differences from the source:
--   - encoding: symmetric zero-diagonal arrays on [n] and local validity → the published unordered-pair Array on Fin n, with inherited local-family conventions; reason: relabeling preserves every input, target, discrepancy and query
--   - encoding: O_C(log n)-bit rational entries → a uniform positive integer B bounds reduced numerator and denominator binary lengths by B times (1+ceil(log₂ n)); reason: equivalent logarithmic bit bound, with B and the threshold allowed to depend on C
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 16, Lemma 4.10 (PDF p. 17); SHA-256 3e49396763fea65b4a7151b904f1cba07f70024d5c851dce84339c98c8148be9

import Mathlib
import Definitions.Def_MetricTesting_Characterization_Supplement_bit_size

set_option autoImplicit false
noncomputable section

namespace MetricTesting.Characterization.Supplement

theorem robust_metric_face :
    ∀ C : ℝ, 2 < C → ∃ C₀ : ℚ, 2 < (C₀ : ℝ) ∧ (C₀ : ℝ) < min C 3 ∧
      ∃ B N : ℕ, 0 < B ∧ 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        ∃ A : Array (BoundedValues (C₀ : ℝ)) n, ∃ H : Finset (Finset (Fin n)),
          (1/20 : ℝ) * (n : ℝ)^2 ≤ H.card ∧ RobustFace C₀ A H ∧ SmallRational B A := by sorry

end MetricTesting.Characterization.Supplement
