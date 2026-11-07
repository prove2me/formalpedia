-- Prove2me | Theorems.Thm_HZTractability_lemma_B_4
-- name    : HZTractability.lemma_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:16:19.603573+00:00
-- url     : https://prove2.me/theorems/f490f214-5185-4203-b476-7b4ccf480032
-- title:
--   Lemma B.4 — approximate price relations
-- statement:
--   Fix a rational $a\in(0,1)$. Under the stated small-error conditions (as in Lemma B.3), let $(p,x)$ be a normalized additive $\varepsilon$-equilibrium of $M(G;a,\tau,K)$ with equalized group prices, and suppose $\mathcal W_u\le\zeta$ for $u=v$ and for every incoming neighbour $u$ of $v$. Then
--   $$
--   |q_v-a^2p_v|+|m_v-ap_v|=O_a(K\varepsilon),\qquad L-O_a(K\varepsilon)\le p_v\le U+2\eta+O_a(K\varepsilon),\qquad q_v<1 .
--   $$
--   All three target prices consequently lie in fixed compact intervals.
--
--   These are the approximate versions of the exact price chain $q_v=am_v=a^2p_v$.
--
--   Differences from the source:
--   - encoding: $O_a(\cdot)$ terms and “sufficiently large” / small-error thresholds, constants depending only on $a$ → one block of existential constants (a threshold $K_a$ or $K_0$, a smallness constant, a multiplier $C_1$) chosen before $K,\tau,G,\varepsilon,\zeta$, the equilibrium and $v$; reason: the paper's convention: constants depend only on $a$, uniformly over the graph, admissible $K$ and $0<\tau\le\kappa/100$ (pp.6, 17, 38)
--   - encoding: “The next three lemmas hold with common constants $K_a$ and $c_a>0$” (p.39) → each of Lemmas B.3, B.4, B.5 has its own $K_a$, $c_a$; reason: the conclusions do not mention $K_a$, $c_a$ and the conditions are monotone, so the maximum of the thresholds and the minimum of the smallness constants serve all three
--   - encoding: “fixed compact intervals” → intervals $[q_0,q_1]$, $[m_0,m_1]$, $[p_0,p_1]$ chosen with the other constants, depending only on $a$; reason: same meaning
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Lemma B.4, p.41 (PDF p.43)

import Mathlib
import Definitions.Def_HZTractability_kappa
import Definitions.Def_HZTractability_admissible
import Definitions.Def_HZTractability_Lp
import Definitions.Def_HZTractability_ThrGraph
import Definitions.Def_HZTractability_Market
import Definitions.Def_HZTractability_IsUnitBundle
import Definitions.Def_HZTractability_IsNormAddEq
import Definitions.Def_HZTractability_decode
import Definitions.Def_HZTractability_WcalV

namespace HZTractability

/-- **Lemma B.4 (Approximate price relations)** (Panageas–Shein–Taherijam–Vazirani,
arXiv:2610.35848, held version, sha256 74b7bf9f…, p.41 (PDF 43)): "Under the stated small-error
conditions, suppose 𝒲_u ≤ ζ for u = v and every incoming neighbor u of v. Then
|q_v − a²p_v| + |m_v − ap_v| = O_a(Kε), L − O_a(Kε) ≤ p_v ≤ U + 2η + O_a(Kε), q_v < 1. All three
target prices consequently lie in fixed compact intervals."

Setting as in Lemma B.3: a normalized additive ε-equilibrium of `M(G; a, τ, K)` with equalized group
prices, `K ≥ K_a` admissible, `K²ε ≤ c_a`, `0 ≤ ζ ≤ c_a`, `0 < τ ≤ κ/100`, `G` nonempty with (2).

**Formalization Note** `O_a(·)` is `C₁ · (·)` with `C₁` depending only on `a`; "fixed compact
intervals" are intervals `[q₀, q₁]`, `[m₀, m₁]`, `[p₀, p₁]` depending only on `a`. All constants
are chosen before `K, τ, G, ε, ζ`, the equilibrium and `v`. -/
theorem lemma_B_4 (a : ℚ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ (Ka : ℕ) (ca C₁ q₀ q₁ m₀ m₁ p₀ p₁ : ℝ), 0 < ca ∧ 0 < C₁ ∧
    ∀ K : ℕ, admissible a K → Ka ≤ K →
    ∀ τ : ℚ, 0 < τ → τ ≤ kappa / 100 → ∀ G : ThrGraph, 1 ≤ G.n → G.Cond2 →
    ∀ (ε ζ : ℝ) (x : Buyer a τ K G → Good a τ K G → ℝ) (p : Good a τ K G → ℝ),
      0 ≤ ε → (K : ℝ) ^ 2 * ε ≤ ca → 0 ≤ ζ → ζ ≤ ca →
      IsNormAddEq (mkt a τ K G) ε x p → IsGroupEqualized p →
      ∀ v : Fin G.n, WcalV x p v ≤ ζ → (∀ u, G.adj u v = true → WcalV x p u ≤ ζ) →
      let A : ℝ := a
      let q := grpMin p v GTag.L
      let m := grpMin p v GTag.M
      let P := grpMin p v GTag.H
      |q - A ^ 2 * P| + |m - A * P| ≤ C₁ * K * ε ∧
      (Lp a K : ℝ) - C₁ * K * ε ≤ P ∧ P ≤ (Up a K : ℝ) + 2 * (eta a τ K : ℝ) + C₁ * K * ε ∧
      q < 1 ∧
      (q₀ ≤ q ∧ q ≤ q₁) ∧ (m₀ ≤ m ∧ m ≤ m₁) ∧ (p₀ ≤ P ∧ P ≤ p₁) := by sorry

end HZTractability
