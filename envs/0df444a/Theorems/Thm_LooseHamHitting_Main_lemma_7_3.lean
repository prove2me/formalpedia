-- Prove2me | Theorems.Thm_LooseHamHitting_Main_lemma_7_3
-- name    : LooseHamHitting.Main.lemma_7_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:19:59.691459+00:00
-- url     : https://prove2.me/theorems/2b7d6160-22c0-4f33-a507-decb5a90d29e
-- title:
--   Lemma 7.3 — a uniform m-edge 3-graph meets near-critical degree lower bounds with probability at least exp{−n^{1/10}}
-- statement:
--   There is an integer $n_0$ such that for every $n\ge n_0$ and every near-critical $(n,m,\ell)$, the probability that a uniform $m$-edge 3-graph on $[n]$ belongs to $\Omega(n,m,\ell)$ satisfies
--   $$\frac{|\Omega(n,m,\ell)|}{\binom{\binom n3}{m}}\ge\exp\{-n^{1/10}\}.$$
--
--   This lower bound pays for conditioning the deletion process on the degree constraints (the factor $\beta^{-1}$ in Claim 8.2).
--
--   Differences from the source: none.
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, p. 27, Lemma 7.3

import Mathlib
import Definitions.Def_LooseHamHitting_Main_Hypergraph
import Definitions.Def_LooseHamHitting_Main_Process
import Definitions.Def_LooseHamHitting_Main_Core

set_option autoImplicit false

open Classical

namespace LooseHamHitting.Main

/-- Lemma 7.3: a uniform `m`-edge 3-graph on `[n]` meets near-critical degree lower bounds with
probability at least `exp{−n^{1/10}}`. -/
theorem lemma_7_3 :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (m : ℕ) (ℓ : Fin n → ℕ), NearCritical n m ℓ →
      Real.exp (-(n : ℝ) ^ ((1 : ℝ) / 10)) ≤
        ((Omega n m ℓ).card : ℝ) / (((n.choose 3).choose m : ℕ) : ℝ) := by sorry

end LooseHamHitting.Main
