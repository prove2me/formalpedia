-- Prove2me | Theorems.Thm_HZTractability_lemma_B_3
-- name    : HZTractability.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:16:42.61054+00:00
-- url     : https://prove2.me/theorems/14943839-2995-4acc-bd27-1181c6da8e58
-- title:
--   Lemma B.3 — preliminary local prices
-- statement:
--   Fix a rational $a\in(0,1)$. Under the stated small-error conditions ($K\ge K_a$ admissible, $K^2\varepsilon\le c_a$, $0\le\zeta\le c_a$, $0<\tau\le\kappa/100$, $G$ nonempty with (2)), let $(p,x)$ be a normalized additive $\varepsilon$-equilibrium of $M(G;a,\tau,K)$ with equalized group prices, and let $v$ be a vertex with $\mathcal W_v\le\zeta$. Then:
--
--   1. the reference prices satisfy
--   $$
--   aL-O_a(\varepsilon)\le r_{Fv}\le a(L+\eta)+O_a(\varepsilon)+\zeta/S^R_{Fv},\qquad aU-O_a(\varepsilon)\le r_{Uv}\le a(U+\eta)+O_a(\varepsilon)+\zeta/S^R_{Uv};
--   $$
--   2. both lie in a fixed compact subinterval of $(1,\infty)$, and for some constant $c>0$, $\max\{r_{Fv},r_{Uv}\}\le1/a-c/K$ and $r_{Uv}-r_{Fv}\ge c/K$;
--   3. the target prices satisfy $q_v\ge ar_{Fv}-O_a(\varepsilon)$, $m_v\ge r_{Fv}-O_a(\varepsilon)$, $p_v\ge r_{Fv}/a-O_a(K\varepsilon)\ge L-O_a(K\varepsilon)$, and
--   $$
--   a^2L-O_a(K\varepsilon)\le q_v\le1+O_a(1/K)<aL-c ;
--   $$
--   4. an optimal dual $(\beta,\mu)$ shared by the floor buyers satisfies $\mu=O_a(\varepsilon)$, $s_R=\beta r_{Fv}+\mu-1=O_a(\varepsilon)$, and $\beta=1/r_{Fv}+O_a(\varepsilon)\ge c$.
--
--   All constants depend only on $a$. No bounds on neighbouring prices are needed.
--
--   Differences from the source:
--   - encoding: $O_a(\cdot)$ terms and “sufficiently large” / small-error thresholds, constants depending only on $a$ → one block of existential constants (a threshold $K_a$ or $K_0$, a smallness constant, a multiplier $C_1$) chosen before $K,\tau,G,\varepsilon,\zeta$, the equilibrium and $v$; reason: the paper's convention: constants depend only on $a$, uniformly over the graph, admissible $K$ and $0<\tau\le\kappa/100$ (pp.6, 17, 38)
--   - encoding: “The next three lemmas hold with common constants $K_a$ and $c_a>0$” (p.39) → each of Lemmas B.3, B.4, B.5 has its own $K_a$, $c_a$; reason: the conclusions do not mention $K_a$, $c_a$ and the conditions are monotone, so the maximum of the thresholds and the minimum of the smallness constants serve all three
--   - encoding: the chain $p_v\ge r_{Fv}/a-O_a(K\varepsilon)\ge L-O_a(K\varepsilon)$ and $q_v\le1+O_a(1/K)<aL-c$ → the bounds $p_v\ge r_{Fv}/a-C_1K\varepsilon$ and $p_v\ge L-C_1K\varepsilon$; $q_v\le1+C_1/K$ and $1+C_1/K<aL-c$; reason: each chain stated through its endpoint bounds with the common constant $C_1$
--   - encoding: “a fixed compact subinterval of $(1,\infty)$” → an interval $[r_0,r_1]$ with $1<r_0\le r_1$, chosen with the other constants; reason: same meaning
--   - reading: “an optimal dual shared by all floor buyers” → every optimal dual of a floor buyer at $v$ (all floor buyers at $v$ share one utility row); reason: the proof derives the bounds for whichever optimal dual is used; this is the stronger reading
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Lemma B.3, pp.39–40 (PDF pp.41–42); small-error conditions, p.39

import Mathlib
import Definitions.Def_HZTractability_kappa
import Definitions.Def_HZTractability_admissible
import Definitions.Def_HZTractability_Lp
import Definitions.Def_HZTractability_ThrGraph
import Definitions.Def_HZTractability_Market
import Definitions.Def_HZTractability_IsUnitBundle
import Definitions.Def_HZTractability_IsNormAddEq
import Definitions.Def_HZTractability_decode
import Definitions.Def_HZTractability_IsOptDual
import Definitions.Def_HZTractability_WcalV

namespace HZTractability

/-- **Lemma B.3 (Preliminary local prices)** (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848,
held version, sha256 74b7bf9f…, pp.39–40 (PDF 41–42)). Under the stated small-error conditions
(p.39: "K ≥ K_a, K²ε ≤ c_a, 0 ≤ ζ ≤ c_a. Here K is admissible and 0 < τ ≤ κ/100"), for a normalized
additive ε-equilibrium of `M(G; a, τ, K)` with equalized group prices (App. B, p.38), if
`𝒲_v ≤ ζ` then, with `q_v, m_v, p_v, r_{Fv}, r_{Uv}` the prices of `L_v, M_v, H_v, RF_v, RU_v`:

1. `aL − O_a(ε) ≤ r_{Fv} ≤ a(L + η) + O_a(ε) + ζ/S^R_{Fv}` and
   `aU − O_a(ε) ≤ r_{Uv} ≤ a(U + η) + O_a(ε) + ζ/S^R_{Uv}`;
2. both references lie in a fixed compact subinterval of `(1, ∞)`, and for some constant `c > 0`,
   `max{r_{Fv}, r_{Uv}} ≤ 1/a − c/K` and `r_{Uv} − r_{Fv} ≥ c/K`;
3. `q_v ≥ a r_{Fv} − O_a(ε)`, `m_v ≥ r_{Fv} − O_a(ε)`, `p_v ≥ r_{Fv}/a − O_a(Kε) ≥ L − O_a(Kε)`,
   and `a²L − O_a(Kε) ≤ q_v ≤ 1 + O_a(1/K) < aL − c`;
4. an optimal dual `(β, μ)` of the floor buyers satisfies `μ = O_a(ε)`,
   `s_R = β r_{Fv} + μ − 1 = O_a(ε)`, `β = 1/r_{Fv} + O_a(ε) ≥ c`.

**Formalization Note** Every `O_a(·)` is `C₁ · (·)` (two-sided as `|·| ≤ C₁ · (·)` where the page
writes `= O_a(·)`) with one constant `C₁` depending only on `a`, chosen together with `K_a`,
`c_a`, the interval `[r₀, r₁] ⊂ (1, ∞)` and `c` before `K, τ, G, ε, ζ`, the equilibrium and
`v`. The chain `p_v ≥ r_{Fv}/a − O_a(Kε) ≥ L − O_a(Kε)` is stated as its two bounds on `p_v`.
The dual statement holds for every optimal dual of a floor buyer at `v` (all floor buyers share
one utility row). -/
theorem lemma_B_3 (a : ℚ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ (Ka : ℕ) (ca C₁ r₀ r₁ c : ℝ), 0 < ca ∧ 0 < C₁ ∧ 1 < r₀ ∧ r₀ ≤ r₁ ∧ 0 < c ∧
    ∀ K : ℕ, admissible a K → Ka ≤ K →
    ∀ τ : ℚ, 0 < τ → τ ≤ kappa / 100 → ∀ G : ThrGraph, 1 ≤ G.n → G.Cond2 →
    ∀ (ε ζ : ℝ) (x : Buyer a τ K G → Good a τ K G → ℝ) (p : Good a τ K G → ℝ),
      0 ≤ ε → (K : ℝ) ^ 2 * ε ≤ ca → 0 ≤ ζ → ζ ≤ ca →
      IsNormAddEq (mkt a τ K G) ε x p → IsGroupEqualized p →
      ∀ v : Fin G.n, WcalV x p v ≤ ζ →
      let A : ℝ := a
      let L : ℝ := Lp a K
      let U : ℝ := Up a K
      let η : ℝ := eta a τ K
      let q := grpMin p v GTag.L
      let m := grpMin p v GTag.M
      let P := grpMin p v GTag.H
      let rF := grpMin p v GTag.RF
      let rU := grpMin p v GTag.RU
      let SRF : ℝ := supCount a τ K (G.outdeg v) GTag.RF
      let SRU : ℝ := supCount a τ K (G.outdeg v) GTag.RU
      (A * L - C₁ * ε ≤ rF ∧ rF ≤ A * (L + η) + C₁ * ε + ζ / SRF) ∧
      (A * U - C₁ * ε ≤ rU ∧ rU ≤ A * (U + η) + C₁ * ε + ζ / SRU) ∧
      (r₀ ≤ rF ∧ rF ≤ r₁ ∧ r₀ ≤ rU ∧ rU ≤ r₁) ∧
      (max rF rU ≤ 1 / A - c / K ∧ c / K ≤ rU - rF) ∧
      (A * rF - C₁ * ε ≤ q ∧ rF - C₁ * ε ≤ m ∧
        rF / A - C₁ * K * ε ≤ P ∧ L - C₁ * K * ε ≤ P) ∧
      (A ^ 2 * L - C₁ * K * ε ≤ q ∧ q ≤ 1 + C₁ / K ∧ 1 + C₁ / K < A * L - c) ∧
      ∀ (k : Fin (popCount a τ K (G.indeg v) (G.outdeg v) BTag.F)) (β μ : ℝ),
        IsOptDual (mkt a τ K G) p (Sum.inl ⟨v, BTag.F, k⟩) β μ →
        |μ| ≤ C₁ * ε ∧ |β * rF + μ - 1| ≤ C₁ * ε ∧ |β - 1 / rF| ≤ C₁ * ε ∧ c ≤ β := by sorry

end HZTractability
