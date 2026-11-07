-- Prove2me | Theorems.Thm_HZTractability_lemma_B_2
-- name    : HZTractability.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:18:57.572029+00:00
-- url     : https://prove2.me/theorems/996f8a19-3bc7-4ee2-b453-263af472d385
-- title:
--   Lemma B.2 — a uniform utility gap
-- statement:
--   Fix a rational $a\in(0,1)$. There are positive rational constants $d_a,g_a,c_a$, depending only on $a$, such that the following holds for all sufficiently large admissible $K$, every rational $\tau\in(0,\kappa/100]$, every nonempty graph $G$ satisfying (2), and every normalized additive $\varepsilon$-equilibrium $(p,x)$ of $M(G;a,\tau,K)$ with $0\le\varepsilon\le c_a$ and prices equalized within each group:
--
--   1. every group valued at one by some buyer has price greater than $1+d_a$;
--   2. every buyer satisfies $V_i(p)\le1-g_a$.
--
--   The gap makes every buyer's budget multiplier bounded below, which powers the demand estimates.
--
--   Differences from the source:
--   - encoding: $O_a(\cdot)$ terms and “sufficiently large” / small-error thresholds, constants depending only on $a$ → one block of existential constants (a threshold $K_a$ or $K_0$, a smallness constant, a multiplier $C_1$) chosen before $K,\tau,G,\varepsilon,\zeta$, the equilibrium and $v$; reason: the paper's convention: constants depend only on $a$, uniformly over the graph, admissible $K$ and $0<\tau\le\kappa/100$ (pp.6, 17, 38)
--   - encoding: “every group valued at one by some buyer has price greater than $1+d_a$”, “$V_i(p)\le1-g_a$” → every good some buyer values at one has price $>1+d_a$ (prices are equalized); no budget-one unit bundle gives buyer $i$ utility above $1-g_a$; reason: with equalized prices a group's price is the price of each of its goods; the maximum of (OptBundle) is attained
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Lemma B.2, p.38 (PDF p.40); standing assumptions of App. B, p.38

import Mathlib
import Definitions.Def_HZTractability_kappa
import Definitions.Def_HZTractability_admissible
import Definitions.Def_HZTractability_Lp
import Definitions.Def_HZTractability_ThrGraph
import Definitions.Def_HZTractability_Market
import Definitions.Def_HZTractability_IsUnitBundle
import Definitions.Def_HZTractability_IsNormAddEq
import Definitions.Def_HZTractability_decode

namespace HZTractability

/-- **Lemma B.2 (A uniform utility gap)** (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848,
held version, sha256 74b7bf9f…, p.38 (PDF 40)): "There are positive rational constants d_a, g_a,
c_a, depending only on a, such that, for all sufficiently large admissible K and ε ≤ c_a, every
group valued at one by some buyer has price greater than 1 + d_a, and every buyer satisfies
V_i(p) ≤ 1 − g_a."

Under the standing assumptions of Appendix B (p.38): a normalized additive ε-equilibrium of
`M(G; a, τ, K)` with prices equalized within each group (Lemma 2.3), uniformly over nonempty
graphs satisfying (2), admissible `K`, and `0 < τ ≤ κ/100`.

**Formalization Note** The constants come first and depend only on `a`; "sufficiently large" is a
threshold `K₀`. With equalized prices "the price of a group" is the price of each of its goods.
`V_i(p) ≤ 1 − g_a` is stated as: no budget-one unit bundle gives buyer `i` utility above
`1 − g_a`. -/
theorem lemma_B_2 (a : ℚ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ (d g c : ℚ), 0 < d ∧ 0 < g ∧ 0 < c ∧ ∃ K₀ : ℕ, ∀ K : ℕ, admissible a K → K₀ ≤ K →
      ∀ τ : ℚ, 0 < τ → τ ≤ kappa / 100 → ∀ G : ThrGraph, 1 ≤ G.n → G.Cond2 →
      ∀ (ε : ℝ) (x : Buyer a τ K G → Good a τ K G → ℝ) (p : Good a τ K G → ℝ),
        0 ≤ ε → ε ≤ c → IsNormAddEq (mkt a τ K G) ε x p → IsGroupEqualized p →
        (∀ j, (∃ i, mkt a τ K G i j = 1) → 1 + (d : ℝ) < p j) ∧
        ∀ i y, IsUnitBundle p y → ∑ j, mkt a τ K G i j * y j ≤ 1 - (g : ℝ) := by sorry

end HZTractability
