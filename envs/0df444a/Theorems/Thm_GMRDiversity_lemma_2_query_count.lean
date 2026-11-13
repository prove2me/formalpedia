-- Prove2me | Theorems.Thm_GMRDiversity_lemma_2_query_count
-- name    : GMRDiversity.lemma_2_query_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:44:20.758205+00:00
-- url     : https://prove2.me/theorems/bb54efb9-9029-4c83-b981-ca8c213b3970
-- title:
--   Proof of Lemma 2, query count — a live-pool policy with $\mathbb E\tau\le C_0(w+2^{n-w})$ for $w\ge5$
-- statement:
--   There is a universal constant $C_0>0$ such that for all $5\le w\le n$ there is a policy $\pi$ with live pool of size $w$ on the parity instance (with $x$ uniform), keeping only queried candidates in its pool, whose number $\tau$ of queries until the target is first queried satisfies
--   $$
--   \mathbb E\tau\le C_0\big(w+2^{n-w}\big).
--   $$
--   The paper's policy builds a nondegenerate subspace of dimension $w-4$ or $w-3$ from $O(w)$ generations, then repeatedly draws seeds, screens their guesses with fresh equations, and synthesizes an accepted guess by recombination; its pool never exceeds $w$ entries and determines its phase.
--
--   **Formalization Note** $C_0$ is chosen before $n$ and $w$; the policy is existential; $\mathbb E\tau$ is the tail sum $\sum_T(1-V^\pi_T)$.
--
--   Differences from the source:
--   - generalization: a policy with live pool of size w → a LivePoolPolicy n w that also satisfies RetainsQueried (next pool = old pool plus the new candidate, with deletions and reordering); reason: such a policy is a live-pool policy under every reading of the page, so the existence statement specializes to the page's
--   - reading: τ = number of queries until the first correct guess is synthesized → the first round at which the target is queried, through expectedHit; reason: the policy stops whenever the target is queried (p.10, 'Stop whenever the target is queried'), so its τ ends at the first query of the target, by synthesis or earlier; Truncation uses τ only through V^π_T ≥ P(τ ≤ T), which needs exactly this τ
--   - reading: the policy π described in Steps (i)–(v) and 'Live pool' → some LivePoolPolicy n w; reason: the page specifies its policy in prose (pool order, the 'generate until' loops, ρ) and uses the bound only to obtain a policy for Lemma 2; the existential is that content
--   - encoding: V^π_T = E[max_{t∈[T]} U_x(z_t)] with x uniform → 2^{-n} Σ_x P(some z_t, t ≤ T, has first coordinate x), with V^π_0 = 0; reason: U_x ∈ {0,1}; the empty maximum is 0
--   - encoding: the general GMR framework of Definition 1 with costs c(Gen_x) = c(XOR) = 1 → only the parity instance: candidates V n × ZMod 2, Gen_x as genLaw, XOR as +, U_x as hit; reason: T counts queries, so costs play no role; the page's statements concern 𝔊^par_x only
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), proof of Lemma 2, 'Query count' and 'Live pool', p.11, and 'Truncation', p.12

import Mathlib
import Definitions.Def_GMRDiversity_expectedHit

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **Proof of Lemma 2: query count** (Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms with
Optimization Guided Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…, proof of Lemma 2,
"Query count" and "Live pool", p.11, and "Truncation", p.12): there is a universal `C₀ > 0` such that
for every `5 ≤ w ≤ n` there is a policy with live pool of size `w` (keeping only queried candidates)
whose expected number of queries until the target is queried satisfies `E τ ≤ C₀(w + 2^{n−w})`.

**Formalization Note.** `C₀` is chosen before `n` and `w`. `w ≥ 5` is the page's case split
("Policy π. For w ≥ 5", p.10); the case `w ≤ 4` is `lemma_2_small_w`. The policy is existential; the
paper constructs it in Steps (i)–(v). `E τ` is `expectedHit`, with `x` uniform. -/
theorem lemma_2_query_count : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ n w : ℕ, 5 ≤ w → w ≤ n →
    ∃ π : LivePoolPolicy n w, π.RetainsQueried ∧
      expectedHit π ≤ ENNReal.ofReal (C₀ * ((w : ℝ) + 2 ^ (n - w))) := by sorry

end GMRDiversity
