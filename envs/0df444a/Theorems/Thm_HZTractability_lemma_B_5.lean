-- Prove2me | Theorems.Thm_HZTractability_lemma_B_5
-- name    : HZTractability.lemma_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:20:29.804567+00:00
-- url     : https://prove2.me/theorems/7e389063-f3c6-47b3-b44d-d78f2b10f96b
-- title:
--   Lemma B.5 — approximate local accounting
-- statement:
--   Fix a rational $a\in(0,1)$. Under the stated small-error conditions (as in Lemma B.3), let $(p,x)$ be a normalized additive $\varepsilon$-equilibrium of $M(G;a,\tau,K)$ with equalized group prices, and suppose $\mathcal W_u\le\zeta$ for every $u\in B_2(v)$. Let $\Phi_v=\Phi_v(p)$ be the residual (16) evaluated with the wire payments (13) at the ideal low and middle prices $a^2p_u$, $ap_u$ and the actual high prices $p_u$, and let $W_v$ and $V_v$ be the actual approved expenditures of the floor and upper buyers on the three targets of $v$. Then
--   $$
--   \Phi_v=W_v+(V_v-c_v)+O_a(K^2\varepsilon+\zeta),\qquad(32)
--   $$
--   $$
--   \Big|\frac{\Phi_v}{2}-\Big(\sum_{u\to v}z_u-\frac12\Big)\Big|\le O_a(1/K+\tau+K^2\varepsilon),\qquad(33)
--   $$
--   where $z_u$ is the decoded value (4).
--
--   The two identities link the sign of the residual to the floor and upper expenditures and to the threshold condition at $v$.
--
--   Differences from the source:
--   - encoding: $O_a(\cdot)$ terms and “sufficiently large” / small-error thresholds, constants depending only on $a$ → one block of existential constants (a threshold $K_a$ or $K_0$, a smallness constant, a multiplier $C_1$) chosen before $K,\tau,G,\varepsilon,\zeta$, the equilibrium and $v$; reason: the paper's convention: constants depend only on $a$, uniformly over the graph, admissible $K$ and $0<\tau\le\kappa/100$ (pp.6, 17, 38)
--   - encoding: “The next three lemmas hold with common constants $K_a$ and $c_a>0$” (p.39) → each of Lemmas B.3, B.4, B.5 has its own $K_a$, $c_a$; reason: the conclusions do not mention $K_a$, $c_a$ and the conditions are monotone, so the maximum of the thresholds and the minimum of the smallness constants serve all three
--   - encoding: $\Phi_v(p)$, $W_v$, $V_v$, $B_2(v)$ → `PhiIdeal`, `floorTargetExp`, `upperTargetExp` (approved expenditure: goods with positive utility), `InB2` (undirected distance at most two); reason: same objects; (32) is stated as an absolute bound on the difference
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Lemma B.5, p.42 (PDF p.44)

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
import Definitions.Def_HZTractability_PhiIdeal

namespace HZTractability

/-- **Lemma B.5 (Approximate local accounting)** (Panageas–Shein–Taherijam–Vazirani,
arXiv:2610.35848, held version, sha256 74b7bf9f…, p.42 (PDF 44)): "Suppose 𝒲_u ≤ ζ for every
u ∈ B_2(v). Under the stated small-error conditions, evaluate the rational wire payments (13) and
residual (16) at the ideal low and middle prices a²p_u, ap_u, keeping the actual high prices p_u.
Denote this residual by Φ_v(p) … Let W_v and V_v be the actual approved expenditures of floor and
upper buyers, respectively, on the three targets of v. Then
(32) Φ_v = W_v + (V_v − c_v) + O_a(K²ε + ζ),
(33) |Φ_v/2 − (∑_{u→v} z_u − 1/2)| ≤ O_a(1/K + τ + K²ε)."

Setting as in Lemma B.3 (equalized group prices, `K ≥ K_a` admissible, `K²ε ≤ c_a`, `0 ≤ ζ ≤ c_a`,
`0 < τ ≤ κ/100`, `G` nonempty with (2)); `z_u` is the decoded value (4) at `u`.

**Formalization Note** `Φ_v(p)` is `PhiIdeal`; `W_v`, `V_v` are `floorTargetExp`,
`upperTargetExp`; `c_v` is the upper-buyer count; `B_2(v)` is undirected distance at most two.
`O_a(·)` is `C₁ · (·)` with `C₁` depending only on `a`, chosen with `K_a, c_a` before everything
else. -/
theorem lemma_B_5 (a : ℚ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ (Ka : ℕ) (ca C₁ : ℝ), 0 < ca ∧ 0 < C₁ ∧
    ∀ K : ℕ, admissible a K → Ka ≤ K →
    ∀ τ : ℚ, 0 < τ → τ ≤ kappa / 100 → ∀ G : ThrGraph, 1 ≤ G.n → G.Cond2 →
    ∀ (ε ζ : ℝ) (x : Buyer a τ K G → Good a τ K G → ℝ) (p : Good a τ K G → ℝ),
      0 ≤ ε → (K : ℝ) ^ 2 * ε ≤ ca → 0 ≤ ζ → ζ ≤ ca →
      IsNormAddEq (mkt a τ K G) ε x p → IsGroupEqualized p →
      ∀ v : Fin G.n, (∀ u, G.InB2 v u → WcalV x p u ≤ ζ) →
      let cv : ℝ := popCount a τ K (G.indeg v) (G.outdeg v) BTag.BMH
      |PhiIdeal p v - (floorTargetExp x p v + (upperTargetExp x p v - cv))|
          ≤ C₁ * ((K : ℝ) ^ 2 * ε + ζ) ∧
      |PhiIdeal p v / 2 -
          ((∑ u ∈ Finset.univ.filter (fun u => G.adj u v = true), decode p u) - 1 / 2)|
          ≤ C₁ * (1 / (K : ℝ) + τ + (K : ℝ) ^ 2 * ε) := by sorry

end HZTractability
