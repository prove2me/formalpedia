-- Prove2me | Theorems.Thm_HopfieldPSpin_Shattering_theorem_4_10
-- name    : HopfieldPSpin.Shattering.theorem_4_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:08:51.966126+00:00
-- url     : https://prove2.me/theorems/64e75048-cba3-4c8b-9175-ce89bfaa57f0
-- title:
--   Theorem 4.10 — replica-symmetric normalization: $2^{-n}Z_n(\beta)/A_n(\beta)\to1$ in probability
-- statement:
--   Fix $\alpha>0$ and $0\le B<\sqrt{2\log2}$. There is $p_0=p_0(\alpha,B)$ such that under (2.2), for either pattern law, each fixed $p\ge p_0$ and $0\le\beta\le B$: with $Z^\circ_n(\beta)=2^{-n}Z_n(\beta)$ and
--   $$A_n(\beta)=\mathbb E[e^{\beta H_n(\sigma)}\mathbf 1_{T_n}]=\exp\Big\{\frac{\beta^2nv_{n,p}}2+o(1)\Big\},$$
--   $A_n(\beta)$ does not depend on $\sigma$, and $Z^\circ_n(\beta)/A_n(\beta)\to1$ in probability as $n\to\infty$.
--
--   It determines the partition function up to a factor $1+o_P(1)$ and gives the replica-symmetric free energy $\frac1n\log Z_n(\beta)\to\log2+\beta^2/2$.
--
--   Differences from the source:
--   - encoding: spins $\sigma\in\{-1,1\}^n$, patterns $k=1,\dots,M$, coordinates $i=1,\dots,n$ → `Config n = Fin n → ℤˣ` (the units of ℤ are exactly ±1), patterns `Fin M`, coordinates `Fin n` (0-based); reason: Lean convention; the same configurations and indices
--   - encoding: $A_n(\beta)$ independent of $\sigma$; $A_n(\beta)=\exp\{\beta^2nv_{n,p}/2+o(1)\}$; convergence in probability → the truncated moment at every σ equals its value at $(1,\dots,1)$; ∃ $e_n\to0$ with $A_n=\exp(\beta^2nv_{n,p}/2+e_n)$ eventually; for every $\epsilon>0$, $\mathbb P(|Z^\circ_n/A_n-1|>\epsilon)\to0$; reason: same statements
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), p. 23 (PDF 25), Theorem 4.10, (4.27)

import Mathlib
import Definitions.Def_HopfieldPSpin_Shattering_Model

open MeasureTheory Filter Topology

namespace HopfieldPSpin.Shattering

/-- Theorem 4.10 (p. 23): for `0 ≤ β ≤ B < √(2 log 2)` and `p ≥ p₀(α, B)`, under (2.2) and
for either pattern law, `A_n(β) = E[e^{β H_n(σ)} 1_{T_n}]` does not depend on `σ`,
`A_n(β) = exp{β² n v_{n,p}/2 + o(1)}`, and `2^{−n} Z_n(β) / A_n(β) → 1` in probability. -/
theorem theorem_4_10 (α B : ℝ) (hα : 0 < α) (hB0 : 0 ≤ B) (hB : B < Real.sqrt (2 * Real.log 2)) :
    ∃ p₀ : ℕ, ∀ p : ℕ, p₀ ≤ p → ∀ M : ℕ → ℕ, StorageCondition p M α →
      ∀ law : PatternLaw, ∀ β : ℝ, 0 ≤ β → β ≤ B →
        (∀ (n : ℕ) (σ : Config n), truncMGF1 n (M n) p law β σ = truncA n (M n) p law β) ∧
        (∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
          truncA n (M n) p law β = Real.exp (β ^ 2 * n * covV n p / 2 + e n)) ∧
        ∀ ϵ : ℝ, 0 < ϵ → Tendsto
          (fun n : ℕ => disorderLaw n (M n) law
            {η | ϵ < |(2 : ℝ)⁻¹ ^ n * partitionFn n (M n) p β η / truncA n (M n) p law β - 1|})
          atTop (𝓝 0) := by sorry

end HopfieldPSpin.Shattering
