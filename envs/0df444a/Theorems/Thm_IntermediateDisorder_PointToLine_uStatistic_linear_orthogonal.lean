-- Prove2me | Theorems.Thm_IntermediateDisorder_PointToLine_uStatistic_linear_orthogonal
-- name    : IntermediateDisorder.PointToLine.uStatistic_linear_orthogonal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:42:25.551724+00:00
-- url     : https://prove2.me/theorems/014f3eb1-145c-4d1a-a34a-ca0e5eb82e36
-- title:
--   Lemma 4.1 (corrected) — $\mathcal S_k^n$ is linear, centred, orthogonal across orders, with $Q[\mathcal S_k^n(g)^2]\le n^{3k/2}\|g\|^2$ for simplex-supported $g$
-- statement:
--   Let the environment $\omega$ be i.i.d. with mean zero and variance one, and fix $n$. Then:
--
--   1. for every $k$, $g\in L^2([0,1]^k\times\mathbb R^k)$ and $\mathbf i\in E_k^n$, the series over $\mathbf x\in\mathbb Z^k$ defining $\mathcal S_k^n(g)$ converges in $L^2(Q)$;
--   2. **linearity:** for $\alpha_1,\dots,\alpha_m\in\mathbb R$ and $g_1,\dots,g_m\in L^2([0,1]^k\times\mathbb R^k)$,
--   $$\sum_{l=1}^m\alpha_l\,\mathcal S_k^n(g_l)=\mathcal S_k^n\Big(\sum_{l=1}^m\alpha_lg_l\Big)\quad\text{with probability one};$$
--   3. **mean zero:** $Q[\mathcal S_k^n(g)]=0$ for every $k\ge1$;
--   4. **orthogonality:** $Q[\mathcal S_{k_1}^n(g_1)\,\mathcal S_{k_2}^n(g_2)]=0$ for $k_1\ne k_2$ and $g_i\in L^2([0,1]^{k_i}\times\mathbb R^{k_i})$;
--   5. **variance bound:** if $g$ vanishes almost everywhere outside $\Delta_k\times\mathbb R^k$, then
--   $$Q\big[\mathcal S_k^n(g)^2\big]\le n^{3k/2}\,\|\bar g_n\|^2_{L^2([0,1]^k\times\mathbb R^k)}\le n^{3k/2}\,\|g\|^2_{L^2([0,1]^k\times\mathbb R^k)} .$$
--
--   This lemma provides the $L^2$ control used in Lemma 4.4 and in the proof of Proposition 5.3 (where it is applied to $\varrho_k$, $n^{k/2}p_k^n$ and their differences, all simplex-supported).
--
--   **Formalization Note** Two corrections of the printed statement. (a) The paper states the variance bound for all $g\in L^2$. As written it fails for $k\ge2$: the proof's identity $Q[\omega(\mathbf i,\mathbf x)\omega(\mathbf i',\mathbf x')]=\mathbf 1\{\mathbf i=\mathbf i',\mathbf x=\mathbf x'\}$ ignores that a permutation of $(\mathbf i,\mathbf x)$ gives the same product. For $k=2$ and $g=\mathbf 1_{A\times B}+\mathbf 1_{B\times A}$ with $A,B$ in disjoint time slabs, $Q[\mathcal S_2^n(g)^2]\approx2n^3\|g\|^2$. The bound holds when $g$ vanishes outside $\Delta_k\times\mathbb R^k$, where only increasing $\mathbf i$ contribute; this is the case stated, and the only case the paper uses. (b) The paper says "for all $k$ the variables $\mathcal S_k^n(g)$ are mean zero"; for $k=0$, $\mathcal S_0^n(g_0)=g_0$ is a constant, so the clause is stated for $k\ge1$. Second moments are written as squared $L^2$ norms in $[0,\infty]$, so none of them is a default value.
-- source:
--   Alberts, Khanin, Quastel, The intermediate disorder regime for directed polymers in dimension 1+1, arXiv:1202.4398v3, p. 22, Lemma 4.1 (variance clause corrected to simplex-supported g; mean-zero clause for k ≥ 1)

import Mathlib
import Definitions.Def_IntermediateDisorder_PointToLine_Environment
import Definitions.Def_IntermediateDisorder_PointToLine_WienerChaos
import Definitions.Def_IntermediateDisorder_PointToLine_UStatistic

namespace IntermediateDisorder.PointToLine

open MeasureTheory ProbabilityTheory

/-- Lemma 4.1 (corrected): the series over `x ∈ ℤ^k` defining `𝒮_k^n(g)` (one for each
`i ∈ E_k^n`) converge in `L²(Q)`; `𝒮_k^n` is
linear; `𝒮_k^n(g)` has mean zero for `k ≥ 1`; `𝒮_{k₁}^n(g₁)` and `𝒮_{k₂}^n(g₂)` are orthogonal
for `k₁ ≠ k₂`; and for `g` vanishing outside `Δ_k × ℝ^k`,
`Q[𝒮_k^n(g)²] ≤ n^{3k/2} ‖ḡ_n‖² ≤ n^{3k/2} ‖g‖²`. -/
theorem uStatistic_linear_orthogonal {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q) (n : ℕ) :
    (∀ (k : ℕ) (g : Lp ℝ 2 (kernelMeasure k)) (i : Fin k → Fin n), Function.Injective i →
      Summable (fun x : Fin k → ℤ => uStatisticTerm ω Q n k g i x)) ∧
    (∀ (k m : ℕ) (α : Fin m → ℝ) (g : Fin m → Lp ℝ 2 (kernelMeasure k)),
      ∑ l, α l • uStatistic ω Q n k (g l) = uStatistic ω Q n k (∑ l, α l • g l)) ∧
    (∀ (k : ℕ), 1 ≤ k → ∀ g : Lp ℝ 2 (kernelMeasure k),
      ∫ a, (uStatistic ω Q n k g : Ω → ℝ) a ∂Q = 0) ∧
    (∀ (k₁ k₂ : ℕ), k₁ ≠ k₂ → ∀ (g₁ : Lp ℝ 2 (kernelMeasure k₁))
      (g₂ : Lp ℝ 2 (kernelMeasure k₂)),
      ∫ a, (uStatistic ω Q n k₁ g₁ : Ω → ℝ) a * (uStatistic ω Q n k₂ g₂ : Ω → ℝ) a ∂Q = 0) ∧
    (∀ (k : ℕ) (g : Lp ℝ 2 (kernelMeasure k)), SimplexSupported g →
      eLpNorm (uStatistic ω Q n k g : Ω → ℝ) 2 Q ^ 2 ≤
          ENNReal.ofReal ((n : ℝ) ^ (3 * (k : ℝ) / 2)) * cellAverageNormSq g n ∧
        ENNReal.ofReal ((n : ℝ) ^ (3 * (k : ℝ) / 2)) * cellAverageNormSq g n ≤
          ENNReal.ofReal ((n : ℝ) ^ (3 * (k : ℝ) / 2)) *
            eLpNorm (g : (Fin k → ℝ × ℝ) → ℝ) 2 (kernelMeasure k) ^ 2) := by sorry

end IntermediateDisorder.PointToLine
