-- Prove2me | Theorems.Thm_MasterVisc_Comparison_lemma_4_1
-- name    : MasterVisc.Comparison.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:46:28.569909+00:00
-- url     : https://prove2.me/theorems/f9e12bba-73aa-472b-8b78-2b10e13be1dd
-- title:
--   Lemma 4.1, p. 958 — [t, T] × 𝒫_L(t, μ) is compact under 𝒲₂
-- statement:
--   Let $(t,\mu)\in\Theta$ and $L>0$. The set $[t,T]\times\mathcal P_L(t,\mu)$ is compact under the pseudometric $\mathcal W_2$ of (2.5): every sequence $(s_n,\mathbb P_n)$ with $t\le s_n\le T$ and $\mathbb P_n\in\mathcal P_L(t,\mu)$ has a subsequence $(s_{n_k},\mathbb P_{n_k})$ and a point $(s^*,\mathbb P^*)\in[t,T]\times\mathcal P_L(t,\mu)$ with
--   $$\lim_{k\to\infty}\mathcal W_2\big((s_{n_k},\mathbb P_{n_k}),(s^*,\mathbb P^*)\big)=0.$$
--
--   This compactness is the key to the viscosity theory: test functions are compared with $V$ only on such sets, and extrema there are attained.
--
--   **Formalization Note.** $\mathcal W_2$ on $\Theta$ is a pseudometric (it compares the stopped laws $\mu_{[0,t]}$), so compactness is stated sequentially; in a pseudometric space sequential compactness and compactness coincide (both reduce to the metric quotient).
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), Lemma 4.1, p. 958

import Mathlib
import Definitions.Def_MasterVisc_Comparison_Setting
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace MasterVisc.Comparison

/-- Lemma 4.1, p. 958: `[t, T] × 𝒫_L(t, μ)` is (sequentially) compact under the pseudometric `𝒲₂` of (2.5). -/
theorem lemma_4_1 {d : ℕ} {T : ℝ≥0} (t : ℝ≥0) (μ : Measure (Path d T)) (ht : t ≤ T)
    (hμ : IsP2 μ) (L : ℝ) (hL : 0 < L) (s : ℕ → ℝ≥0) (P : ℕ → Measure (Path d T))
    (hs : ∀ n, t ≤ s n ∧ s n ≤ T) (hP : ∀ n, InPL L t μ (P n)) :
    ∃ (φ : ℕ → ℕ) (s' : ℝ≥0) (P' : Measure (Path d T)),
      StrictMono φ ∧ t ≤ s' ∧ s' ≤ T ∧ InPL L t μ P' ∧
      Tendsto (fun k => W2Θ (s (φ k)) (P (φ k)) s' P') atTop (𝓝 0) := by sorry

end MasterVisc.Comparison
