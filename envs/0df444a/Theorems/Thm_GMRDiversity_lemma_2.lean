-- Prove2me | Theorems.Thm_GMRDiversity_lemma_2
-- name    : GMRDiversity.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:42:30.584149+00:00
-- url     : https://prove2.me/theorems/eff9bd39-26b6-4793-ba01-fc78be86385f
-- title:
--   Lemma 2 — a policy with live pool of size $w$ succeeds within $T\le C(w+2^{n-w})$ queries
-- statement:
--   There is a constant $C>0$ such that for every $n\ge2$ and $1\le w\le n$ there is a policy $\pi$ with live pool of size $w$ on the parity instance $\mathfrak G^{\mathrm{par}}_x$ (with $x$ uniform) and a horizon $T\le C(w+2^{n-w})$ such that
--   $$
--   V^\pi_T\ge\tfrac23.
--   $$
--   This is the upper-bound half of Theorem 3.
--
--   **Formalization Note** $C$ is chosen before $n$ and $w$; the policy is required to keep only queried candidates in its pool.
--
--   Differences from the source:
--   - generalization: a policy with live pool of size w → a LivePoolPolicy n w that also satisfies RetainsQueried (next pool = old pool plus the new candidate, with deletions and reordering); reason: such a policy is a live-pool policy under every reading of the page, so the existence statement specializes to the page's
--   - encoding: live pool size w up to time T → pool length ≤ w at every round; reason: V^π_T depends only on rounds ≤ T; a policy obeying the bound up to T can be changed after T (keep the empty list) without changing V^π_T
--   - encoding: V^π_T = E[max_{t∈[T]} U_x(z_t)] with x uniform → 2^{-n} Σ_x P(some z_t, t ≤ T, has first coordinate x), with V^π_0 = 0; reason: U_x ∈ {0,1}; the empty maximum is 0
--   - encoding: the general GMR framework of Definition 1 with costs c(Gen_x) = c(XOR) = 1 → only the parity instance: candidates V n × ZMod 2, Gen_x as genLaw, XOR as +, U_x as hit; reason: T counts queries, so costs play no role; the page's statements concern 𝔊^par_x only
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), Lemma 2, p.10

import Mathlib
import Definitions.Def_GMRDiversity_value

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **Lemma 2** (Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms with Optimization Guided
Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…, Lemma 2, p.10): there is `C > 0` such
that for every `n ≥ 2` and `1 ≤ w ≤ n` there is a policy `π` with live pool of size `w` and
`T ≤ C(w + 2^{n−w})` such that `V^π_T(𝔊^par_x) ≥ 2/3`.

**Formalization Note.** `C` is chosen before `n` and `w`. The policy is required to keep only queried
candidates (`RetainsQueried`), the strictest reading of "live pool"; the paper's policy does. -/
theorem lemma_2 : ∃ C : ℝ, 0 < C ∧ ∀ n w : ℕ, 2 ≤ n → 1 ≤ w → w ≤ n →
    ∃ π : LivePoolPolicy n w, π.RetainsQueried ∧
      ∃ T : ℕ, (T : ℝ) ≤ C * ((w : ℝ) + 2 ^ (n - w)) ∧ 2 / 3 ≤ value π T := by sorry

end GMRDiversity
