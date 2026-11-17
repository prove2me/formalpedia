-- Prove2me | Theorems.Thm_HZTractability_Supplement_theorem_5_7
-- name    : HZTractability.Supplement.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:31:48.423194+00:00
-- url     : https://prove2.me/theorems/be5b81fb-7a90-4229-8490-260797d13bff
-- title:
--   Theorem 5.7 — uniform robustness of the minimum-price decoder
-- statement:
--   Fix $\kappa=1/200$. For every rational $a$ with $0<a<1$ there are positive rational constants $\tau_a\le\kappa/100$, $e_a$, $B_a$, $\nu_a$, $M_a$ and an integer $K_a\ge1$, depending only on $a$, such that the following holds for every admissible $K\ge K_a$ and every threshold graph $G$ with $n\ge1$ vertices satisfying (2). Let $N$ be the number of buyers of the market $\mathcal M(G;a,\tau_a,K)$ (with $\eta=\tau_a w$). Then
--   $$\nu_aK^2n\le N\le M_aK^2n,$$
--   and for every $0<\varepsilon\le e_a/K^2$ and every normalized additive $\varepsilon$-equilibrium $(x,p)$ of the market, the decoded vector $z_v=\mathrm{clip}\big((\min_{j\in H_v}p_j-L)/w\big)$ fails the $\kappa$-threshold constraint at at most
--   $$B_a\,N\,\varepsilon$$
--   vertices.
--
--   At constant accuracy the decoder is no longer exactly correct, but its errors are proportional to $N\varepsilon$; combined with the size bound this gives the forward reduction from weak threshold games (Proposition 5.8) used for Theorem 1.2.
--
--   **Formalization Note** The market, the admissibility condition (20), restriction (2), the equilibrium notion and the decoder (4) are the base mission's published definitions; failures are counted with `failSet`. The equilibrium is arbitrary (prices need not be equalized within groups).
--
--   Differences from the source:
--   - encoding: N, n, κ, the market M(G; a, τa, K) with η = τa w, the minimum-price decoder → Fintype.card (Buyer a τa K G), G.n, kappa = 1/200, the published mkt a τa K G (η built in) and decode p; reason: the base mission's published objects; the same instances
--   - encoding: fails the κ-threshold condition at at most Ba N ε vertices → (failSet kappa G (decode p)).card ≤ Ba · N · ε; reason: failSet is the exact negation of the per-vertex clause of IsThresholdSol
--   - encoding: 0 < ε ≤ ea/K² → ε : ℝ with 0 < ε ≤ ea/K²; reason: the theorem does not restrict ε to rationals; a real ε covers every instance of the source
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Theorem 5.7, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_HZTractability_kappa
import Definitions.Def_HZTractability_admissible
import Definitions.Def_HZTractability_ThrGraph
import Definitions.Def_HZTractability_Market
import Definitions.Def_HZTractability_IsNormAddEq
import Definitions.Def_HZTractability_decode
import Definitions.Def_HZTractability_Supplement_failSet

namespace HZTractability.Supplement

open HZTractability

/-- **Theorem 5.7 (Uniform robustness)** (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848, held
version, sha256 74b7bf9f…, p.23 (PDF 25)): "For every fixed rational a ∈ (0, 1), there are positive
rational constants τa ≤ κ/100, ea, Ba, νa, Ma, and an integer Ka ≥ 1, depending only on a, such that
the following holds. For every admissible K ≥ Ka and every nonempty graph satisfying (2), the market
M(G; a, τa, K), with η = τa w, has νa K² n ≤ N ≤ Ma K² n. For every 0 < ε ≤ ea/K², the minimum-price
decoder applied to any normalized additive ε-equilibrium fails the κ-threshold condition at at most
Ba N ε vertices."

**Formalization Note** `κ = 1/200` (`kappa`); `n = G.n`; `N` is the number of buyers of the published
market `mkt a τa K G` (its `η = τa w` is built in); "admissible" is the published `admissible` (20)
and "(2)" is `ThrGraph.Cond2`. The constants form one `∃` block after `a` and before `K`, `G`, `ε` and
the equilibrium. The equilibrium is arbitrary (prices need not be equalized); the error is `ε`, real;
the decoder is the published minimum-price `decode` (4); failures are counted by `failSet`. -/
theorem theorem_5_7 (a : ℚ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ (τa ea Ba νa Ma : ℚ) (Ka : ℕ), 0 < τa ∧ τa ≤ kappa / 100 ∧ 0 < ea ∧ 0 < Ba ∧ 0 < νa ∧
      0 < Ma ∧ 1 ≤ Ka ∧
      ∀ K : ℕ, admissible a K → Ka ≤ K → ∀ G : ThrGraph, 1 ≤ G.n → G.Cond2 →
        (νa * (K : ℚ) ^ 2 * G.n ≤ (Fintype.card (Buyer a τa K G) : ℚ) ∧
          (Fintype.card (Buyer a τa K G) : ℚ) ≤ Ma * (K : ℚ) ^ 2 * G.n) ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ (ea : ℝ) / (K : ℝ) ^ 2 →
        ∀ (x : Buyer a τa K G → Good a τa K G → ℝ) (p : Good a τa K G → ℝ),
          IsNormAddEq (mkt a τa K G) ε x p →
          ((failSet (kappa : ℝ) G (decode p)).card : ℝ) ≤
            (Ba : ℝ) * (Fintype.card (Buyer a τa K G) : ℝ) * ε := by sorry

end HZTractability.Supplement
