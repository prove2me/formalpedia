-- Prove2me | Theorems.Thm_MinCostMaj_lemma_termination
-- name    : MinCostMaj.lemma_termination
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:12:57.704202+00:00
-- url     : https://prove2.me/theorems/315443a2-d594-40a0-9a9a-250156bbc58a
-- title:
--   Lemma "Termination" — the level procedure stops within $|A^J_v|+1$ iterations
-- statement:
--   Fix a variable $v$ with potato $A^J_v$ and LP marginals $\lambda_v$ (a probability vector on $A^J_v$). For every threshold sequence with $t_i\in[2^{-i},2^{-(i-1)}]$ for all $i\ge1$, the level procedure started at $L=1$ reaches a good level after at most $|A^J_v|$ updates of $L$, that is, it terminates after at most $|A^J_v|+1$ iterations.
--
--   Hence the level $L(v)$ is well defined.
--
--   Differences from the source:
--   - reading: the level procedure terminates after at most |A^J_v| + 1 iterations → for every threshold sequence in the sampling range, some iterate step^[n](1) with n ≤ |A^J_v| is a good level; reason: n non-terminal iterations followed by the terminal one; the claim is deterministic
--   - encoding: LP marginal λ_v → any probability vector on A^J_v; reason: the BLP marginals are such vectors
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Lemma "Termination", p.21 (PDF p.22)

import Mathlib
import Definitions.Def_MinCostMaj_Levels

namespace MinCostMaj

/-- **Lemma "Termination"**, p.21 (PDF p.22).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Lemma "Termination", p.21: "For every variable v, the level procedure terminates after at most
|A^J_v| + 1 iterations."

For every threshold sequence with `tᵢ ∈ [2^{−i}, 2^{−(i−1)}]` for all `i ≥ 1`, some iterate
`step^[n] 1` with `n ≤ |A^J_v|` is a good level: at most `|A^J_v|` non-terminal iterations, then the
terminal one.

**Formalization Note.** Deterministic: it holds for every such sequence, not only almost surely.
`S = A^J_v`, `lam = λᵥ` a probability vector on `S`. -/
theorem lemma_termination {D : Type*} [DecidableEq D] (S : Finset D) (lam : D → ℝ)
    (hlam : IsProbVec S lam) (t : ℕ → ℝ)
    (ht : ∀ i, 1 ≤ i → ((1 : ℝ) / 2) ^ i ≤ t i ∧ t i ≤ 2 * ((1 : ℝ) / 2) ^ i) :
    ∃ n ≤ S.card, IsGood S lam t ((step S lam t)^[n] 1) := by sorry

end MinCostMaj
