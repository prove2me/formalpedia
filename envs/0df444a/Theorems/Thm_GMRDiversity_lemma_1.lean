-- Prove2me | Theorems.Thm_GMRDiversity_lemma_1
-- name    : GMRDiversity.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:42:46.727179+00:00
-- url     : https://prove2.me/theorems/45fe4752-5b39-49b7-bb4d-f0918219d473
-- title:
--   Lemma 1 — a policy with live pool size at most $w$ needs $T\ge c(w+2^{n-w})$ queries
-- statement:
--   There exists a constant $c>0$ such that for every $n\ge 2$ and $1\le w\le n$, every $T\in\mathbb N$, and every policy $\pi$ with live pool size at most $w$ on the parity instance $\mathfrak G^{\mathrm{par}}_x$ (with $x$ uniform),
--   $$
--   V^\pi_T\ge\tfrac23\quad\Longrightarrow\quad T\ge c\,\big(w+2^{n-w}\big).
--   $$
--   This is the lower-bound half of Theorem 3: recombination never enlarges the span of the live pool, so a small pool forces either many generations or a long wait for a lucky one.
--
--   **Formalization Note** $c$ is chosen before $n$, $w$, $\pi$ and $T$.
--
--   Differences from the source:
--   - generalization: every policy with live pool size at most w → every LivePoolPolicy n w, whose next pool may hold any element of the F₂-span of the previous pool and the new candidate; reason: this class contains the page's policies under every reading of 'previously queried candidates', so the bound for it implies the page's
--   - encoding: live pool size w up to time T → pool length ≤ w at every round; reason: V^π_T depends only on rounds ≤ T; a policy obeying the bound up to T can be changed after T (keep the empty list) without changing V^π_T
--   - encoding: V^π_T = E[max_{t∈[T]} U_x(z_t)] with x uniform → 2^{-n} Σ_x P(some z_t, t ≤ T, has first coordinate x), with V^π_0 = 0; reason: U_x ∈ {0,1}; the empty maximum is 0
--   - encoding: the general GMR framework of Definition 1 with costs c(Gen_x) = c(XOR) = 1 → only the parity instance: candidates V n × ZMod 2, Gen_x as genLaw, XOR as +, U_x as hit; reason: T counts queries, so costs play no role; the page's statements concern 𝔊^par_x only
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), Lemma 1, p.9

import Mathlib
import Definitions.Def_GMRDiversity_value

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **Lemma 1** (Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms with Optimization Guided
Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…, Lemma 1, p.9): there exists `c > 0`
such that for every `n ≥ 2` and `1 ≤ w ≤ n`, `T ∈ ℕ`, and every policy `π` with live pool size at
most `w`, if `V^π_T(𝔊^par_x) ≥ 2/3`, then `T ≥ c(w + 2^{n−w})`.

**Formalization Note.** `c` is chosen before `n`, `w`, `π`, `T`. A `LivePoolPolicy n w` may keep any
element of the span of its old pool and the new candidate, which contains the paper's class. -/
theorem lemma_1 : ∃ c : ℝ, 0 < c ∧ ∀ n w : ℕ, 2 ≤ n → 1 ≤ w → w ≤ n →
    ∀ (π : LivePoolPolicy n w) (T : ℕ), 2 / 3 ≤ value π T →
      c * ((w : ℝ) + 2 ^ (n - w)) ≤ T := by sorry

end GMRDiversity
