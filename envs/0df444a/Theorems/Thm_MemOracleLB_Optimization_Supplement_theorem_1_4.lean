-- Prove2me | Theorems.Thm_MemOracleLB_Optimization_Supplement_theorem_1_4
-- name    : MemOracleLB.Optimization.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:13:14.363459+00:00
-- url     : https://prove2.me/theorems/9953610f-72eb-46c7-ac02-7181d7f5dac0
-- title:
--   Theorem 1.4 — Distinguishing the hard pair
-- statement:
--   Let $n=m+1$. Draw independent rows $R_i\sim N(0,I_n/n)$, a label $j$ uniformly from $\{1,2\}$, and the algorithm's internal seed independently of both. For $b_1=1$, $b_2=3$ and $L=\ell n$, set
--   $$K_j(R)=\{x\in\mathbb R^n:\ |\langle R_i,x\rangle|\le1\ (i<n),\ |\langle R_n,x\rangle|\le b_jL\}.$$
--   There are absolute constants $a>0$, $\ell_0>3$ and $N\ge2$ such that for all $n\ge N$ and $\ell\ge\ell_0$, every randomized algorithm which identifies $j$ from an ordinary membership oracle for $K_j(R)$ with joint probability at least $2/3$ satisfies
--   $$\mathbb E_{R,j,\omega}T_j\ge a\frac{n^2}{(\log n)^2}.$$
--
--   Here $T_j$ is the number of membership queries before halting, with infinite cost if the run never halts; identification means halting with the exact label $j$. The expectation averages the two labels with equal weight. The matrix and its last row are hidden. The bodies in this theorem are $K_j(R)$ themselves. This companion theorem states the distinguishing lower bound supplied by the hard distribution and is not used in the proof of the mission's goal.
--
--   Differences from the source:
--   - reading: L is a sufficiently large universal constant times n, chosen in Section 4 → L = ℓn for every ℓ ≥ ℓ₀, with a and N uniform in ℓ; reason: this is the stronger reading prescribed in the brief; the localization argument needs only L ≥ 2C₀²n/ε₀ and otherwise has constants independent of ℓ
--   - encoding: an algorithm with only the membership oracle as input → the published OracleAlgorithm evaluated at fixed objective input 0; reason: every input-free algorithm extends to this interface by ignoring the objective, and no matrix row is supplied
--   - encoding: dimension n and an independent uniform j in {1,2} → n = m + 1 and j : Fin 2 labels the output j.val + 1, with b = 1 or 3; probability and expectation are half the sum under matrixLaw.prod P; reason: zero-based indexing and the product law express exactly the two labels and all three independent randomness sources
--   - encoding: Ω(n²/log² n) for sufficiently large dimension → positive universal a and threshold N ≥ 2, query counts in ℕ∞ and expectations in ℝ≥0∞; reason: explicit asymptotic quantifiers preserve infinite runs and avoid zero logarithmic denominators
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), Theorem 1.4, PDF p. 4 (printed p. 3); proof PDF p. 21 (printed p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_MemOracleLB_Optimization_OracleModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u1_4
noncomputable section

namespace MemOracleLB.Optimization.Supplement

/-- Theorem 1.4, PDF p.4. The algorithm sees only the ordinary membership oracle;
its fixed objective input 0 provides no information about R or the hidden label. -/
theorem theorem_1_4 :
    ∃ a ℓ₀ : ℝ, 0 < a ∧ 3 < ℓ₀ ∧ ∃ N : ℕ, 2 ≤ N ∧
    ∀ m : ℕ, N ≤ m + 1 → ∀ ℓ : ℝ, ℓ₀ ≤ ℓ →
    ∀ (Ω : Type u1_4) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (A : OracleAlgorithm (m + 1) Ω),
      (2 / 3 : ℝ≥0∞) ≤ (1 / 2 : ℝ≥0∞) *
        ∑ j : Fin 2, ((matrixLaw (m + 1)).prod P)
          {p | Outputs (fun h => A.action 0 h p.2)
            (membershipOracle (hardBody p.1 (ℓ * (m + 1)) (if j.val = 0 then 1 else 3)))
            ((j.val + 1 : ℕ) : ℝ)} →
      ENNReal.ofReal (a * (m + 1 : ℝ) ^ 2 / (Real.log (m + 1)) ^ 2) ≤
        (1 / 2 : ℝ≥0∞) * ∑ j : Fin 2,
          ∫⁻ p, (queries A
            (hardBody p.1 (ℓ * (m + 1)) (if j.val = 0 then 1 else 3)) 0 p.2).toENNReal
            ∂((matrixLaw (m + 1)).prod P) := by sorry

end MemOracleLB.Optimization.Supplement
