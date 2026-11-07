-- Prove2me | Theorems.Thm_HZTractability_lemma_4_9
-- name    : HZTractability.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:16:15.095558+00:00
-- url     : https://prove2.me/theorems/f4d84504-ec15-4579-b227-55e92cbbfac5
-- title:
--   Lemma 4.9 — unapproved expenditure $\mathcal W\le C_aN\varepsilon$
-- statement:
--   Fix a rational $a\in(0,1)$. There are positive rational constants $d_a,g_a,c_a,C_a$, depending only on $a$, such that for every sufficiently large admissible $K$, every rational $\tau\in(0,\kappa/100]$, every nonempty graph $G$ satisfying (2), and every normalized additive $\varepsilon$-equilibrium of $M(G;a,\tau,K)$ with equalized group prices and
--   $$
--   0\le\varepsilon\le\min\{c_a,1/(C_aK)\},
--   $$
--   the total unapproved expenditure satisfies
--   $$
--   \mathcal W\le C_aN\varepsilon,
--   $$
--   where $N$ is the number of buyers. Moreover every group valued at one has price greater than $1+d_a$, and every buyer has optimal utility at most $1-g_a$.
--
--   This turns the per-buyer error $\varepsilon=\varepsilon^*(a)/N$ into a bounded total of misplaced spending.
--
--   Differences from the source:
--   - encoding: $O_a(\cdot)$ terms and “sufficiently large” / small-error thresholds, constants depending only on $a$ → one block of existential constants (a threshold $K_a$ or $K_0$, a smallness constant, a multiplier $C_1$) chosen before $K,\tau,G,\varepsilon,\zeta$, the equilibrium and $v$; reason: the paper's convention: constants depend only on $a$, uniformly over the graph, admissible $K$ and $0<\tau\le\kappa/100$ (pp.6, 17, 38)
--   - encoding: “every group valued at one by some buyer has price greater than $1+d_a$”, “$V_i(p)\le1-g_a$” → every good some buyer values at one has price $>1+d_a$ (prices are equalized); no budget-one unit bundle gives buyer $i$ utility above $1-g_a$; reason: with equalized prices a group's price is the price of each of its goods; the maximum of (OptBundle) is attained
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Lemma 4.9, pp.17–18 (PDF pp.19–20); standing assumptions of §4.5, p.17

import Mathlib
import Definitions.Def_HZTractability_kappa
import Definitions.Def_HZTractability_admissible
import Definitions.Def_HZTractability_Lp
import Definitions.Def_HZTractability_ThrGraph
import Definitions.Def_HZTractability_Market
import Definitions.Def_HZTractability_IsUnitBundle
import Definitions.Def_HZTractability_IsNormAddEq
import Definitions.Def_HZTractability_decode
import Definitions.Def_HZTractability_Wcal

namespace HZTractability

/-- **Lemma 4.9 (Unapproved expenditure)** (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848,
held version, sha256 74b7bf9f…, pp.17–18 (PDF 19–20)): "There are positive rational constants d_a,
g_a, c_a, C_a, depending only on a, such that for every sufficiently large admissible K, every
normalized additive ε-equilibrium with ε ≤ min{c_a, 1/(C_a K)} satisfies 𝒲 ≤ C_a N ε. Every group
valued at one has price greater than 1 + d_a, and every buyer has optimal utility at most 1 − g_a."

Here `𝒲` is the total unapproved expenditure (§4.5, p.17) and `N` the number of buyers of
`M(G; a, τ, K)`. Standing assumptions of §4.5 (p.17): prices are equalized within each group
(Lemma 2.3), and the constants are uniform over nonempty graphs satisfying (2), admissible `K`, and
`0 < τ ≤ κ/100`.

**Formalization Note** As in Lemma B.2: constants first, "sufficiently large" as a threshold
`K₀`, `V_i(p) ≤ 1 − g_a` in bundle form, `ε ≥ 0` as in Definition 2.2. -/
theorem lemma_4_9 (a : ℚ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ (d g c Ca : ℚ), 0 < d ∧ 0 < g ∧ 0 < c ∧ 0 < Ca ∧ ∃ K₀ : ℕ,
      ∀ K : ℕ, admissible a K → K₀ ≤ K →
      ∀ τ : ℚ, 0 < τ → τ ≤ kappa / 100 → ∀ G : ThrGraph, 1 ≤ G.n → G.Cond2 →
      ∀ (ε : ℝ) (x : Buyer a τ K G → Good a τ K G → ℝ) (p : Good a τ K G → ℝ),
        0 ≤ ε → ε ≤ min (c : ℝ) (1 / ((Ca : ℝ) * K)) →
        IsNormAddEq (mkt a τ K G) ε x p → IsGroupEqualized p →
        Wcal (mkt a τ K G) x p ≤ (Ca : ℝ) * Fintype.card (Buyer a τ K G) * ε ∧
        (∀ j, (∃ i, mkt a τ K G i j = 1) → 1 + (d : ℝ) < p j) ∧
        ∀ i y, IsUnitBundle p y → ∑ j, mkt a τ K G i j * y j ≤ 1 - (g : ℝ) := by sorry

end HZTractability
