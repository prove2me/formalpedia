-- Prove2me | Theorems.Thm_HZTractability_theorem_4_1
-- name    : HZTractability.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:15:36.074853+00:00
-- url     : https://prove2.me/theorems/a1fd49a0-a229-4e46-95e2-609ffe174ff2
-- title:
--   Theorem 4.1 — soundness of the market construction
-- statement:
--   For every rational $a\in(0,1)$ there are positive rational constants $\tau_a$ (with $\tau_a\le\kappa/100$) and $\varepsilon^*(a)$ and an integer $K_a$, depending only on $a$, such that the following holds. For every admissible $K\ge K_a$ and every nonempty graph $G$ satisfying (2), every normalized additive $\varepsilon^*(a)/N$-equilibrium of $M(G;a,\tau_a,K)$, where $N$ is its number of buyers, decodes to values satisfying, at every vertex $v$,
--   $$
--   \sum_{u\to v}z_u>\tfrac12+\kappa\ \Longrightarrow\ z_v\le\kappa,\qquad \sum_{u\to v}z_u<\tfrac12-\kappa\ \Longrightarrow\ z_v\ge1-\kappa .
--   $$
--   Thus the decoded vector is a solution of the threshold game.
--
--   This is the correctness of the reduction behind Theorem 1.1. The equilibrium is arbitrary: prices need not be equalized, since the decoder uses group minima.
--
--   Differences from the source:
--   - encoding: positive rational $\tau_a$ → $0<\tau_a\le\kappa/100$; reason: $M(G;a,\tau,K)$ is defined only for $0<\tau\le\kappa/100$ (§3.2, p.11; display (9), p.13)
--   - encoding: “decodes to values satisfying, at every vertex, …” → `IsThresholdSol κ G (decode p)`, which also contains $z\in[0,1]^V$; reason: every clipped vector lies in $[0,1]^V$
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Theorem 4.1, p.12 (PDF p.14); ε*(a) defined p.19 (PDF p.21)

import Mathlib
import Definitions.Def_HZTractability_kappa
import Definitions.Def_HZTractability_admissible
import Definitions.Def_HZTractability_Lp
import Definitions.Def_HZTractability_ThrGraph
import Definitions.Def_HZTractability_Market
import Definitions.Def_HZTractability_IsUnitBundle
import Definitions.Def_HZTractability_IsNormAddEq
import Definitions.Def_HZTractability_decode
import Definitions.Def_HZTractability_IsThresholdSol

namespace HZTractability

/-- **Theorem 4.1 (Soundness of the market construction)** (Panageas–Shein–Taherijam–Vazirani,
arXiv:2610.35848, held version, sha256 74b7bf9f…, p.12 (PDF 14); ε*(a) defined p.19 (PDF 21)):
"For every fixed rational a ∈ (0, 1), there are positive rational constants τ_a, ε∗(a) and an
integer K_a, depending only on a, with the following property. For every K ≥ K_a admissible as in
Subsection 4.4 and every nonempty graph G satisfying (2), every normalized additive
ε∗(a)/N-equilibrium of M(G; a, τ_a, K) decodes to values satisfying, at every vertex,
∑_{u→v} z_u > 1/2 + κ ⟹ z_v ≤ κ, ∑_{u→v} z_u < 1/2 − κ ⟹ z_v ≥ 1 − κ. Thus the decoded vector is a
solution of the threshold game."

**Formalization Note** `N` is the number of buyers of `M(G; a, τ_a, K)`. The equilibrium is
arbitrary (prices need not be equalized); the decoder (4) uses the minimum price of each high
group. `τ_a ≤ κ/100` because `M(G; a, τ, K)` is defined for `0 < τ ≤ κ/100` (§3.2, p.11; (9), p.13). The
conclusion is `IsThresholdSol`, whose `[0, 1]` clause holds for every clipped vector. -/
theorem theorem_4_1 (a : ℚ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ (τa εs : ℚ) (Ka : ℕ), 0 < τa ∧ τa ≤ kappa / 100 ∧ 0 < εs ∧
      ∀ K : ℕ, admissible a K → Ka ≤ K → ∀ G : ThrGraph, 1 ≤ G.n → G.Cond2 →
      ∀ (x : Buyer a τa K G → Good a τa K G → ℝ) (p : Good a τa K G → ℝ),
        IsNormAddEq (mkt a τa K G) ((εs : ℝ) / Fintype.card (Buyer a τa K G)) x p →
        IsThresholdSol (kappa : ℝ) G (decode p) := by sorry

end HZTractability
