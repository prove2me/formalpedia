-- Prove2me | Theorems.Thm_GMRDiversity_lemma_1_display
-- name    : GMRDiversity.lemma_1_display
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:42:59.240191+00:00
-- url     : https://prove2.me/theorems/dd8e91a1-af05-4739-bfab-b3f475343c02
-- title:
--   Proof of Lemma 1 — $V^\pi_T\le 2^{-n}+\sum_{j=1}^T2^{\min\{w,j-1\}-n}$
-- statement:
--   For every live-pool policy $\pi$ with pool size at most $w$ on the parity instance, and every $T\in\mathbb N$,
--   $$
--   V^\pi_T\le 2^{-n}+\sum_{j=1}^{T}2^{\min\{w,j-1\}-n}.
--   $$
--   The term $2^{-n}$ is the probability that $x=0$; otherwise $x$ must enter the span of the live pool for the first time at some generation $j\le T$, which has probability at most $2^{\min\{w,j-1\}-n}$.
--
--   Differences from the source:
--   - generalization: n ≥ 2 and 1 ≤ w ≤ n (the hypotheses of Lemma 1) → every n and w; reason: the derivation of the display uses none of them; the page's case is a special case
--   - generalization: every policy with live pool size at most w → every LivePoolPolicy n w, whose next pool may hold any element of the F₂-span of the previous pool and the new candidate; reason: this class contains the page's policies under every reading of 'previously queried candidates', so the bound for it implies the page's
--   - encoding: live pool size w up to time T → pool length ≤ w at every round; reason: V^π_T depends only on rounds ≤ T; a policy obeying the bound up to T can be changed after T (keep the empty list) without changing V^π_T
--   - encoding: V^π_T = E[max_{t∈[T]} U_x(z_t)] with x uniform → 2^{-n} Σ_x P(some z_t, t ≤ T, has first coordinate x), with V^π_0 = 0; reason: U_x ∈ {0,1}; the empty maximum is 0
--   - encoding: the general GMR framework of Definition 1 with costs c(Gen_x) = c(XOR) = 1 → only the parity instance: candidates V n × ZMod 2, Gen_x as genLaw, XOR as +, U_x as hit; reason: T counts queries, so costs play no role; the page's statements concern 𝔊^par_x only
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), proof of Lemma 1, p.10

import Mathlib
import Definitions.Def_GMRDiversity_value

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **Proof of Lemma 1: the value bound** (Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms
with Optimization Guided Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…, proof of
Lemma 1, p.10): for every policy `π` with live pool size at most `w` and every `T`,
`V^π_T ≤ 2^{−n} + ∑_{j=1}^T 2^{min{w, j−1} − n}`.

**Formalization Note.** The right-hand side is written `(1 + ∑_{j=1}^T 2^{min{w, j−1}}) / 2ⁿ`. The
statement is asserted for all `n` and `w`, without the lemma's `n ≥ 2`, `1 ≤ w ≤ n`, which the
page's derivation of this display does not use. -/
theorem lemma_1_display {n w : ℕ} (π : LivePoolPolicy n w) (T : ℕ) :
    value π T ≤ (1 + ∑ j ∈ Finset.Icc 1 T, (2 : ℝ) ^ min w (j - 1)) / 2 ^ n := by sorry

end GMRDiversity
