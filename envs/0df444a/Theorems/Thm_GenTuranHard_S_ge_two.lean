-- Prove2me | Theorems.Thm_GenTuranHard_S_ge_two
-- name    : GenTuranHard.S_ge_two
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:48.501431+00:00
-- url     : https://prove2.me/theorems/922f0c9a-dd7c-43b2-975c-606a77181cd0
-- title:
--   p.17 — $S(\mathbf x, n)$ is an integer at least $2$
-- statement:
--   Let $T$ be a bipartite graph with $e(T) > 0$, let $n \ge 1$, and let $\mathbf x$ be defined as in (4.3). Then $S(\mathbf x, n)$ is an integer and
--
--   $$
--   S(\mathbf x, n) \ge 2.
--   $$
--
--   This lower bound is used to show $a + b + v(Z)^{v(T)-\varepsilon} = o(S)$ (p.21).
--
--   **Formalization Note** $S(\mathbf x, n)$ is defined as a natural number, so integrality is built in.
--
--   Differences from the source:
--   - encoding: sums over Q ∈ 𝒬_T of f_Q(x)·(…) with f_Q a sum over sequences with T_s ≅ Q → sums directly over the sequences of (4.1), grouped by p(T_s); reason: regrouping a finite sum; hom(·,G), v(·), p(·) are isomorphism-invariant, so the values are equal
--   - generalization: v(T) ≥ 3 (the standing assumption of §4, p.12) → every bipartite T with e(T) > 0 (v(T) ≥ 2, s = v(T) − 2 ≥ 0); reason: for v(T) = 2 the construction is L_x(G) = G with the empty sequence; the source's case v(T) ≥ 3 is included
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), §4.1, p.17 (after the proof of Lemma 4.6)

import Mathlib
import Definitions.Def_GenTuranHard_A0

set_option autoImplicit false

namespace GenTuranHard

/-- **S(x, n) is an integer greater than 1** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256
dc85633a…, §4.1, p.17, after the proof of Lemma 4.6). For the §4 graph `T` (bipartite, `e(T) > 0`),
`x` as in (4.3) and `n ≥ 1`, `S(x, n) ≥ 2`.

**Formalization Note** `S(x, n)` is `Sx`, a natural number by definition, so integrality is built in. -/
theorem S_ge_two {W : Type} [Fintype W] (T : SimpleGraph W) (hT : T.IsBipartite)
    (hTe : T.edgeSet.Nonempty) (n : ℕ) (hn : 1 ≤ n) :
    2 ≤ Sx T (xVec (Fintype.card W) n) n := by sorry

end GenTuranHard
