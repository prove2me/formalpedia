-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_theorem_1_7
-- name    : FracColorLocal.KrFree.theorem_1_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:13:37.604901+00:00
-- url     : https://prove2.me/theorems/d28547cd-8454-4a72-84e6-d9792a13a888
-- title:
--   Theorem 1.7 — α_u(G) ≥ c_r Φ_{G,u}(s) for K_r-free G, with rational c_r ∈ (0, 1] and c_r ≥ κ₁/r
-- statement:
--   For every integer $r\ge4$ there is a rational constant $c_r\in(0,1]$ such that the following holds. Let $G$ be a finite $K_r$-free graph, $s$ a positive real vertex weight and $u$ a nonnegative real vertex weight. Then
--
--   $$\alpha_u(G)\ \ge\ c_r\,\Phi_{G,u}(s)=c_r\sum_{v}u(v)\,f\big(d_{G,s}(v)\big).$$
--
--   Moreover, $c_r$ can be chosen so that $c_r\ge\kappa_1/r$ for an absolute constant $\kappa_1>0$: one $\kappa_1$ works for every $r$.
--
--   This weighted Shearer-type bound is the paper's main structural result; through Lemma 3.1 it yields Corollary 1.8 and Theorem 1.5.
--
--   Differences from the source:
--   - encoding: "a $K_r$-free graph $G$" → a graph on a finite type `V : Type`; reason: every finite graph is isomorphic to one on such a type.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 4 (PDF 5), Theorem 1.7

import Mathlib
import Definitions.Def_FracColorLocal_KrFree_PhiColoring
import Definitions.Def_FracColorLocal_KrFree_Potential

namespace FracColorLocal.KrFree

/-- Theorem 1.7: for every `r ≥ 4` a rational `c_r ∈ (0, 1]` with `α_u(G) ≥ c_r Φ_{G,u}(s)` for all
`K_r`-free `G`, positive `s` and nonnegative `u`; moreover `c_r ≥ κ₁/r` for one absolute `κ₁ > 0`. -/
theorem theorem_1_7 :
    ∃ κ₁ : ℝ, 0 < κ₁ ∧
      ∀ r : ℕ, 4 ≤ r →
        ∃ c : ℚ, 0 < c ∧ c ≤ 1 ∧ κ₁ / r ≤ (c : ℝ) ∧
          ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree r →
            ∀ s u : V → ℝ, (∀ v, 0 < s v) → (∀ v, 0 ≤ u v) →
              (c : ℝ) * phiPot G u s ≤ weightedIndepNumber G u := by sorry

end FracColorLocal.KrFree
