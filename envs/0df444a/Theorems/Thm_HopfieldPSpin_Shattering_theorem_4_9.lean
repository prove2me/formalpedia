-- Prove2me | Theorems.Thm_HopfieldPSpin_Shattering_theorem_4_9
-- name    : HopfieldPSpin.Shattering.theorem_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:09:37.227847+00:00
-- url     : https://prove2.me/theorems/71667a67-b55b-4724-819f-3bf8b958aebd
-- title:
--   Theorem 4.9 — uniform one- and two-replica truncated Laplace estimates (4.23)–(4.24), errors $O(n^{-(p-4)/2})$
-- statement:
--   Fix $\alpha>0$ and a finite $S\ge0$. There is $p_0=p_0(\alpha,S)\ge5$ such that under the storage condition (2.2), for each fixed $p\ge p_0$ (and either pattern law),
--   $$\log\mathbb E[e^{sH_n(\sigma)}\mathbf 1_{T_n}]=\frac{s^2n}2v_{n,p}+o(1),\qquad \log\mathbb E[e^{s(H_n(\sigma)+H_n(\tau))}\mathbf 1_{T_n}]=s^2n\big(v_{n,p}+Q_{n,p}(\sigma,\tau)\big)+o(1)$$
--   uniformly over all $\sigma,\tau\in\Sigma_n$ and $|s|\le S$; for fixed parameters both uniform errors are $O(n^{-(p-4)/2})$.
--
--   The $o(1)$ precision is what makes the second moment of the truncated partition function asymptotic to the square of its first moment.
--
--   Differences from the source:
--   - encoding: spins $\sigma\in\{-1,1\}^n$, patterns $k=1,\dots,M$, coordinates $i=1,\dots,n$ → `Config n = Fin n → ℤˣ` (the units of ℤ are exactly ±1), patterns `Fin M`, coordinates `Fin n` (0-based); reason: Lean convention; the same configurations and indices
--   - encoding: uniform $o(1)$ errors; uniform $O(n^{-(p-4)/2})$ errors → `LaplaceOne` / `LaplaceTwo` on $[-S,S]$ (one sequence $e_n\to0$ bounding the error for all large $n$, all σ, τ, $|s|\le S$) and ∃ C with both errors $\le Cn^{-(p-4)/2}$ eventually, uniformly; reason: the paper's uniform asymptotics; the pattern law is quantified as in the standing assumptions
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), p. 22 (PDF 24), Theorem 4.9, (4.23)–(4.24)

import Mathlib
import Definitions.Def_HopfieldPSpin_Shattering_Model
import Definitions.Def_HopfieldPSpin_Shattering_Shattered

open MeasureTheory Filter Topology

namespace HopfieldPSpin.Shattering

/-- Theorem 4.9 (p. 22): under (2.2), for every `p ≥ p₀(α, S)`, the Laplace estimates (4.23)
and (4.24) hold with `o(1)` errors uniform over `σ, τ ∈ Σ_n` and `|s| ≤ S`, and both errors are
`O(n^{−(p−4)/2})`. -/
theorem theorem_4_9 (α S : ℝ) (hα : 0 < α) (hS : 0 ≤ S) :
    ∃ p₀ : ℕ, 5 ≤ p₀ ∧ ∀ p : ℕ, p₀ ≤ p → ∀ M : ℕ → ℕ, StorageCondition p M α →
      ∀ law : PatternLaw,
        LaplaceOne p M law (Set.Icc (-S) S) ∧ LaplaceTwo p M law (Set.Icc (-S) S) ∧
        ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ σ τ : Config n, ∀ s : ℝ, |s| ≤ S →
          |Real.log (truncMGF1 n (M n) p law s σ) - s ^ 2 * n / 2 * covV n p| ≤
              C * (n : ℝ) ^ (-(((p : ℝ) - 4) / 2)) ∧
          |Real.log (truncMGF2 n (M n) p law s σ τ) - s ^ 2 * n * (covV n p + covQ n p σ τ)| ≤
              C * (n : ℝ) ^ (-(((p : ℝ) - 4) / 2)) := by sorry

end HopfieldPSpin.Shattering
