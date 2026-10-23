-- Prove2me | Theorems.Thm_MNLTrisection_Adaptive_lemma_10
-- name    : MNLTrisection.Adaptive.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:49.24006+00:00
-- url     : https://prove2.me/theorems/474a4d21-37b2-4635-9f82-5fb00be797fa
-- title:
--   Lemma 10, p. 13 — regret in Case 2: the recursion of ψ²_τ into ψ¹, ψ², ψ³ at epoch τ + 1
-- statement:
--   Throughout, there are $N$ items with known revenues $r_i \in [0,1]$ and unknown utilities $v_i \ge 0$, the no-purchase utility is $v_0 = 1$, and $R(S) = \sum_{j\in S} r_j v_j/(1+\sum_{j\in S} v_j)$ is the expected revenue (2) of an assortment $S \subseteq [N]$. Run the adaptive-confidence trisection policy for $T$ periods, with $\varepsilon_\tau = \tfrac13(\tfrac23)^\tau$ and $n_\tau = 8\lceil \varepsilon_\tau^{-2}\ln(8T\varepsilon_\tau^2)\rceil$, and let $\psi^\omega_\tau(\alpha,\beta)$ be the conditional regrets (14). There is a universal constant $C > 0$ such that for all $N$, $v$, $r$, every $T \ge 25$, every epoch $\tau$ with $\sum_{\tau'<\tau} n_{\tau'} < T$ and all $\alpha, \beta \ge 0$, there are parameters $\alpha_1', \beta_1'(\Delta), \alpha_2', \beta_2', \alpha_3', \beta_3' \ge 0$ with $\beta_1'(\Delta) \le \Delta$ (for $\Delta > \varepsilon_\tau$) and $\alpha_3' \le 3\varepsilon_\tau$ such that
--   $$\psi^2_\tau(\alpha,\beta) \le C\varepsilon_\tau^{-1}\log(T\varepsilon_\tau^2) + \psi^2_{\tau+1}(\alpha_2',\beta_2') + \psi^3_{\tau+1}(\alpha_3',\beta_3')\cdot C\frac{\log(T\varepsilon_\tau^2)}{T\varepsilon_\tau^2} + \sup_{\Delta>\varepsilon_\tau}\psi^1_{\tau+1}(\alpha_1',\beta_1'(\Delta))\,e^{-n_\tau\Delta^2}.$$
--
--   This is the recursion for the case where the optimal level is still inside the search interval: the epoch costs $O(\varepsilon_\tau^{-1}\log(T\varepsilon_\tau^2))$, and the next epoch falls into one of the three cases with controlled probabilities.
--
--   **Formalization Note** The exponent's $\Delta_\tau$ is read as the supremum variable $\Delta$. The cases follow the statement's labels (the proof's case list on Supplement p. 7 swaps the labels of Cases 1 and 2). $O(\cdot)$ is a universal $C$ chosen before every other quantity. $T \ge 25$ and "epoch $\tau$ can start" are added so that $\log(T\varepsilon_\tau^2) > 0$. Inner-iteration counts are $\max(1, n_\tau)$; $\psi$ is $0$ on null conditioning events.
-- source:
--   Chen, Wang & Zhou, An Optimal Policy for Dynamic Assortment Planning Under Uncapacitated Multinomial Logit Models, arXiv:1805.04785v2, p. 13, Lemma 10 and (14); proof in Supplement pp. 4–7 (PDF 23–26)

import Mathlib
import Definitions.Def_MNLTrisection_Adaptive_Model

namespace MNLTrisection.Adaptive

/-- **Lemma 10** (Regret in Case 2, p. 13). For a universal `C`, every `T ≥ 25`, every epoch `τ`
that can start and all `α, β ≥ 0`, there are parameters `α'₁, β'₁(Δ), α'₂, β'₂, α'₃, β'₃ ≥ 0`
with `β'₁(Δ) ≤ Δ` and `α'₃ ≤ 3ε_τ` such that
`ψ²_τ(α, β) ≤ C ε_τ^{-1} log(Tε_τ²) + ψ²_{τ+1}(α'₂, β'₂) + ψ³_{τ+1}(α'₃, β'₃) · C log(Tε_τ²)/(Tε_τ²)
  + sup_{Δ > ε_τ} ψ¹_{τ+1}(α'₁, β'₁(Δ)) exp{−n_τ Δ²}`. -/
theorem lemma_10 :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (v r : Fin N → ℝ), (∀ i, 0 ≤ v i) →
      (∀ i, r i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ T τ : ℕ, 25 ≤ T → ∑ τ' ∈ Finset.range τ, nEpoch T τ' < T →
      ∀ α β : ℝ, 0 ≤ α → 0 ≤ β →
      ∃ (α₁ : ℝ) (β₁ : ℝ → ℝ) (α₂ β₂ α₃ β₃ : ℝ),
        0 ≤ α₁ ∧ (∀ Δ : ℝ, eps τ < Δ → 0 ≤ β₁ Δ ∧ β₁ Δ ≤ Δ) ∧ 0 ≤ α₂ ∧ 0 ≤ β₂ ∧
        0 ≤ α₃ ∧ 0 ≤ β₃ ∧ α₃ ≤ 3 * eps τ ∧
        psi v r T 2 τ α β ≤
          C * (eps τ)⁻¹ * Real.log (T * eps τ ^ 2) + psi v r T 2 (τ + 1) α₂ β₂ +
            psi v r T 3 (τ + 1) α₃ β₃ * (C * (Real.log (T * eps τ ^ 2) / (T * eps τ ^ 2))) +
            ⨆ Δ : {Δ : ℝ // eps τ < Δ},
              psi v r T 1 (τ + 1) α₁ (β₁ Δ) * Real.exp (-((nEpoch T τ : ℝ) * (Δ : ℝ) ^ 2)) := by sorry

end MNLTrisection.Adaptive
