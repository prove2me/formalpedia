-- Prove2me | Theorems.Thm_KaelblingPOMDP_Witness_witness_theorem
-- name    : KaelblingPOMDP.Witness.witness_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:56.803756+00:00
-- url     : https://prove2.me/theorems/266c0746-118a-4e95-88b2-5eb975a5dd44
-- title:
--   §4.4.2, p. 116 — the witness theorem: Q̂^a_t differs from Q^a_t iff some p_new beats all of U_a at some b
-- statement:
--   Let $\langle S, A, T, R, \Omega, O\rangle$ be a POMDP satisfying the standing hypotheses, $t \ge 2$ and $a$ an action. Let $U_a$ be a nonempty finite set of $t$-step trees with root action $a$ whose subtrees lie in $\mathcal V_{t-1}$, and $\hat Q^a_t(b) = \max_{p \in U_a} V_p(b)$. Then the following are equivalent:
--
--   1. there is a belief state $b$ with $\hat Q^a_t(b) \ne Q^a_t(b)$;
--   2. there are $p \in U_a$, an observation $o$, a tree $p' \in \mathcal V_{t-1}$ and a belief state $b$ such that
--   $$V_{p_{\mathrm{new}}}(b) > V_{\tilde p}(b) \quad \text{for all } \tilde p \in U_a,$$
--   where $p_{\mathrm{new}}$ agrees with $p$ except that $o(p_{\mathrm{new}}) = p'$.
--
--   Such a $b$ is a **witness**. If no tree of $U_a$ can be improved by replacing a single subtree, there are no witness points and $U_a$ represents the Q-function exactly. This is the stopping criterion of the witness algorithm.
--
--   **Formalization Note** "The true Q-function differs from the approximate Q-function" is read as "they differ at some belief state". $Q^a_t$ is the formula of p. 114 (`Qfun`). Here $t = n + 2$.
-- source:
--   Kaelbling, Littman, Cassandra, Planning and acting in partially observable stochastic domains, Artificial Intelligence 101:99–134 (1998), DOI 10.1016/S0004-3702(98)00023-X, p. 116, §4.4.2, condition (1)

import Mathlib
import Definitions.Def_KaelblingPOMDP_Witness_Useful

namespace KaelblingPOMDP.Witness

open Finset

universe u

/-- The witness theorem, §4.4.2, p. 116 (Kaelbling, Littman, Cassandra, *Planning and acting in partially observable stochastic domains*,
Artificial Intelligence 101:99–134 (1998)): "The true Q-function, Q^a_t, differs
from the approximate Q-function, Q̂^a_t, if and only if there is some p ∈ U_a, o ∈ Ω, and p′ ∈ V_{t−1}
for which there is some b such that V_{p_new}(b) > V_p̃(b), for all p̃ ∈ U_a."
Here `t = n + 2`, `U_a` is a nonempty set of candidate t-step trees (root `a`, subtrees in
`V_{t−1}`), `Q̂^a_t(b) = max_{p ∈ U_a} V_p(b)`, `Q^a_t` is the Q-function of p. 114, and
`p_new = p.replace o p'`.

**Formalization Note** "Differs" is read as "differs at some belief state"; all belief states
range over `stdSimplex ℝ S`. -/
theorem witness_theorem {S A Ω : Type u} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (M : POMDP S A Ω) (hM : M.IsValid) (a : A) (n : ℕ)
    (U : Finset (PolicyTree A Ω (n + 1))) (hU : U.Nonempty) (hUC : U ⊆ candidates M a n) :
    (∃ b ∈ stdSimplex ℝ S, upper M U hU b ≠ Qfun M a n b) ↔
      ∃ p ∈ U, ∃ o : Ω, ∃ p' ∈ usefulTrees M n, ∃ b ∈ stdSimplex ℝ S,
        ∀ q ∈ U, valueAt M q b < valueAt M (p.replace o p') b := by sorry

end KaelblingPOMDP.Witness
