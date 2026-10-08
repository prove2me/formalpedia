-- Prove2me | Theorems.Thm_KaelblingPOMDP_Witness_subtree_swap
-- name    : KaelblingPOMDP.Witness.subtree_swap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:06.839949+00:00
-- url     : https://prove2.me/theorems/60cf0edc-3060-4cfe-995c-39d2925794d4
-- title:
--   Appendix A, proof of Theorem A.1, p. 131 — replacing one subtree of p by that of p* improves on p at b
-- statement:
--   Let $\langle S, A, T, R, \Omega, O\rangle$ be a POMDP satisfying the standing hypotheses and let $p, p^*$ be $t$-step policy trees ($t \ge 2$) with the same root action. If $b$ is a belief state with
--   $$V_{p^*}(b) > V_p(b),$$
--   then there is an observation $o^*$ such that the tree $p_{\mathrm{new}}$, identical to $p$ except that in the place of the subtree $o^*(p)$ it has $o^*(p^*)$, satisfies
--   $$V_{p_{\mathrm{new}}}(b) > V_p(b).$$
--
--   This is the step of the proof of Theorem A.1 that reduces an arbitrary improving tree to one that differs from a tree of $U_a$ in a single subtree.
--
--   **Formalization Note** The paper's choice of $o^*$ on p. 131 prints a comparison of $\sum_s b(s) \sum_{s'} T(s, a(p^*), s') V_{o^*(\cdot)}(s')$ without the observation probability $O(s', a(p^*), o^*)$; the subsequent displays carry it. The statement here is the conclusion the proof draws, with $V_{p_{\mathrm{new}}}$ given by the value recursion.
-- source:
--   Kaelbling, Littman, Cassandra, Planning and acting in partially observable stochastic domains, Artificial Intelligence 101:99–134 (1998), DOI 10.1016/S0004-3702(98)00023-X, p. 131, Appendix A, proof of Theorem A.1

import Mathlib
import Definitions.Def_KaelblingPOMDP_Witness_Useful

namespace KaelblingPOMDP.Witness

open Finset

universe u

/-- Appendix A, proof of Theorem A.1, p. 131 (Kaelbling, Littman, Cassandra, *Planning and acting in partially observable stochastic domains*,
Artificial Intelligence 101:99–134 (1998)): if two trees `p`, `p*` with the same
root action satisfy `V_{p*}(b) > V_p(b)` at a belief state `b`, then there is an observation `o*` such that
the tree `p_new` obtained from `p` by putting `o*(p*)` in the place of the subtree `o*(p)` satisfies
`V_{p_new}(b) > V_p(b)`.

**Formalization Note** The paper's choice of `o*` on p. 131 prints the comparison
`Σ_s b(s) Σ_{s'} T(s, a(p*), s') V_{o*(p*)}(s') > Σ_s b(s) Σ_{s'} T(s, a(p*), s') V_{o*(p)}(s')`
without the factor `O(s', a(p*), o*)`; the statement here is the conclusion the proof draws,
`V_{p_new}(b) > V_p(b)`, with `V_{p_new}` given by the value recursion (which carries the factor). -/
theorem subtree_swap {S A Ω : Type u} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (M : POMDP S A Ω) (hM : M.IsValid) {n : ℕ} (p pstar : PolicyTree A Ω (n + 1))
    (ha : pstar.action = p.action) (b : S → ℝ) (hb : b ∈ stdSimplex ℝ S)
    (hlt : valueAt M p b < valueAt M pstar b) :
    ∃ o : Ω, valueAt M p b < valueAt M (p.replace o (pstar.subtree o)) b := by sorry

end KaelblingPOMDP.Witness
