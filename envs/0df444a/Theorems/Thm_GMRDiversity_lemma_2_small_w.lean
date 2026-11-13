-- Prove2me | Theorems.Thm_GMRDiversity_lemma_2_small_w
-- name    : GMRDiversity.lemma_2_small_w
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:44:37.71406+00:00
-- url     : https://prove2.me/theorems/efc6c322-9b3e-4aab-8f6e-814f508c3d6c
-- title:
--   Proof of Lemma 2 — the generate-only policy: $V_T=1-(1-2^{-n})^T$, $\mathbb E\tau=2^n$
-- statement:
--   Let $\pi$ be the policy that generates a fresh candidate in every round and keeps an empty pool. For all $n$ and $w$:
--
--   1. $\pi$ keeps only queried candidates (its pool is empty), so it is a policy with live pool of size $w$;
--   2. each query hits the target with probability $2^{-n}$, so for every $T$
--   $$
--   V^\pi_T=1-\big(1-2^{-n}\big)^T;
--   $$
--   3. the expected number of queries until the target is queried is $\mathbb E\tau=2^n$, and $2^n\le 16\cdot2^{n-w}$ when $w\le4$;
--   4. truncating after $3\cdot2^n$ queries gives success probability at least $2/3$: $V^\pi_{3\cdot2^n}\ge 2/3$.
--
--   This settles the upper bound when $w\le4$.
--
--   Differences from the source:
--   - generalization: the case w ≤ 4 → every n and w, except the clause 2^n ≤ 16·2^{n−w}, which keeps w ≤ 4; reason: the generate-only policy has an empty pool, so it is a live-pool policy for every w; the page's case is a special case
--   - encoding: the expected number of queries → expectedHit, the tail sum Σ_T (1 − V_T); reason: tail-sum formula for E τ
--   - encoding: V^π_T = E[max_{t∈[T]} U_x(z_t)] with x uniform → 2^{-n} Σ_x P(some z_t, t ≤ T, has first coordinate x), with V^π_0 = 0; reason: U_x ∈ {0,1}; the empty maximum is 0
--   - encoding: the general GMR framework of Definition 1 with costs c(Gen_x) = c(XOR) = 1 → only the parity instance: candidates V n × ZMod 2, Gen_x as genLaw, XOR as +, U_x as hit; reason: T counts queries, so costs play no role; the page's statements concern 𝔊^par_x only
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), proof of Lemma 2, p.10

import Mathlib
import Definitions.Def_GMRDiversity_expectedHit
import Definitions.Def_GMRDiversity_genOnly

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **Proof of Lemma 2: the case `w ≤ 4`** (Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms
with Optimization Guided Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…, proof of
Lemma 2, p.10): the policy that repeatedly generates fresh candidates keeps only queried candidates
(its pool is empty); each query hits the target with probability `2^{−n}`, so
`V_T = 1 − (1 − 2^{−n})^T`; the expected number of queries is `2ⁿ`, which is at most
`16 · 2^{n−w}` when `w ≤ 4`; and truncating after `3 · 2ⁿ` queries gives success probability at
least `2/3`.

**Formalization Note.** The policy `genOnly n w` is a live-pool policy for every `w`, so the
statement is made for every `n` and `w`; the inequality `2ⁿ ≤ 16 · 2^{n−w}` keeps the page's
hypothesis `w ≤ 4`. -/
theorem lemma_2_small_w (n w : ℕ) :
    (genOnly n w).RetainsQueried ∧
    (∀ T : ℕ, value (genOnly n w) T = 1 - (1 - ((2 : ℝ) ^ n)⁻¹) ^ T) ∧
    expectedHit (genOnly n w) = 2 ^ n ∧
    (w ≤ 4 → (2 : ℝ) ^ n ≤ 16 * 2 ^ (n - w)) ∧
    2 / 3 ≤ value (genOnly n w) (3 * 2 ^ n) := by sorry

end GMRDiversity
