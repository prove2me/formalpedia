-- Prove2me | Theorems.Thm_KaelblingPOMDP_Witness_parsimonious_representation
-- name    : KaelblingPOMDP.Witness.parsimonious_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:33.690012+00:00
-- url     : https://prove2.me/theorems/c8d0c1ab-c25e-4db1-93d4-48b59563ca38
-- title:
--   §4.2, p. 112 — the useful trees form the unique minimal subset representing the same value function
-- statement:
--   Let $\langle S, A, T, R, \Omega, O\rangle$ be a POMDP satisfying the standing hypotheses and let $\tilde V$ be a finite nonempty set of policy trees of the same depth. Call $p \in \tilde V$ useful in $\tilde V$ when its dominance region $R(\alpha_p, \tilde V)$ is nonempty, and let $W \subseteq \tilde V$ be the set of useful trees. Then:
--
--   1. **$W$ represents the same value function.** $W$ is nonempty and
--   $$\max_{p \in W} V_p(b) = \max_{p \in \tilde V} V_p(b) \quad \text{for every belief state } b.$$
--   2. **$W$ is minimal.** If $W' \subseteq \tilde V$ is nonempty and $\max_{p \in W'} V_p(b) = \max_{p \in \tilde V} V_p(b)$ for every belief state $b$, then for every $p \in W$ there is $q \in W'$ with $V_q = V_p$.
--
--   With trees identified by their value functions, as in footnote 6, (1) and (2) say that $W$ is the unique minimal subset of $\tilde V$ that represents the same value function: the paper's parsimonious representation. A tree is useful precisely when it is a component of it.
--
--   **Formalization Note** The conclusion of (2) compares value functions (`value M q = value M p`), not trees, as footnote 6 requires.
-- source:
--   Kaelbling, Littman, Cassandra, Planning and acting in partially observable stochastic domains, Artificial Intelligence 101:99–134 (1998), DOI 10.1016/S0004-3702(98)00023-X, p. 112, §4.2, with footnote 6 and the definition of R(α, V)

import Mathlib
import Definitions.Def_KaelblingPOMDP_Witness_Useful

namespace KaelblingPOMDP.Witness

open Finset

universe u

/-- §4.2, p. 112 (Kaelbling, Littman, Cassandra, *Planning and acting in partially observable stochastic domains*,
Artificial Intelligence 101:99–134 (1998)): "Given a set of policy trees, Ṽ, it is possible
to define a unique minimal subset V that represents the same value function." The set of useful trees
of a finite nonempty set `W` of trees (those whose region `R(α_p, W)` is nonempty)

1. **represents** the same value function: it is nonempty and its upper surface equals that of `W`
   at every belief state;
2. is **minimal**: every nonempty subset `W'` of `W` that represents the same value function contains,
   for every useful tree `p`, a tree with the same value function as `p`.

Together these say that the useful set is the unique minimal representing subset, with trees
identified by their value functions (footnote 6, p. 112).

**Formalization Note** Footnote 6 identifies trees with equal value functions; the conclusion of (2)
is therefore `value M q = value M p`, not `q = p`. -/
theorem parsimonious_representation {S A Ω : Type u} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (M : POMDP S A Ω) (hM : M.IsValid) {n : ℕ} (W : Finset (PolicyTree A Ω n)) (hW : W.Nonempty) :
    (∃ hU : (usefulSet M W).Nonempty,
        ∀ b ∈ stdSimplex ℝ S, upper M (usefulSet M W) hU b = upper M W hW b) ∧
      ∀ (W' : Finset (PolicyTree A Ω n)) (hW' : W'.Nonempty), W' ⊆ W →
        (∀ b ∈ stdSimplex ℝ S, upper M W' hW' b = upper M W hW b) →
        ∀ p ∈ usefulSet M W, ∃ q ∈ W', value M q = value M p := by sorry

end KaelblingPOMDP.Witness
