-- Prove2me | Theorems.Thm_NonmonotoneSubmod_Nonadaptive_nonadaptive_one_third
-- name    : NonmonotoneSubmod.Nonadaptive.nonadaptive_one_third
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T06:51:04.063055+00:00
-- url     : https://prove2.me/theorems/833b6548-70e6-43d9-aecc-8c2734aa960e
-- title:
--   Theorem 2.6 — Algorithm NA achieves $(1/3 - 4/(9n))\,OPT$
-- statement:
--   Let $X$ be a nonempty finite ground set with $n = |X|$ elements and let $f : 2^X \to \mathbb{R}_{\ge 0}$ be a nonnegative submodular function with optimum $OPT = \max_{S \subseteq X} f(S)$. Let $\omega$ be the averaged marginal value of Definition 2.4, and let $\tilde\omega : X \to \mathbb{R}$ be any estimates satisfying
--
--   $$
--   |\tilde\omega(x) - \omega(x)| < \frac{OPT}{n^2} \quad \text{for every } x \in X .
--   $$
--
--   Algorithm NA returns a uniformly random set $R = X(1/2)$ with probability $8/9$, and the set $A = \{x \in X : \tilde\omega(x) > 0\}$ with probability $1/9$. Its expected value satisfies
--
--   $$
--   \frac{8}{9}\,\mathbf{E}[f(X(1/2))] + \frac{1}{9}\, f(A) \ \ge\ \Big(\frac13 - \frac{4}{9n}\Big)\, OPT .
--   $$
--
--   This is the paper's Theorem 2.6, "Algorithm NA achieves expected value at least $(1/3 - o(1))\,OPT$": a nonadaptive algorithm, which queries sets chosen in advance and then returns a set computed from the answers, beats the factor $1/4$ that a uniformly random set achieves.
--
--   **Formalization Note** Three points pin down the printed statement. (1) The printed $o(1)$ is the explicit term $4/(9n)$ that the proof establishes (last display on p. 1140). (2) The guarantee holds on the accuracy event of NA's first step, "find $\tilde\omega(x)$ such that $|\tilde\omega(x) - \omega(x)| < OPT/n^2$ with high probability"; that event is taken as a hypothesis on arbitrary estimates $\tilde\omega$, with the strict inequality as printed, and the sampling that makes it likely (Lemma 2.5) is not part of this statement. (3) The left-hand side is the expected value NA returns given $\tilde\omega$: $R$ is sampled independently of $\tilde\omega$ and the choice between $R$ and $A$ is an independent coin. The expectation $\mathbf{E}[f(X(1/2))]$ is the exact uniform average over the $2^n$ subsets of $X$. The ground set is assumed nonempty so that the divisions by $n$ are genuine. When $OPT = 0$ the accuracy hypothesis cannot hold, but then $f \equiv 0$ and the conclusion is trivially true in any case.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1139, Theorem 2.6 and Algorithm NA; explicit constant from the proof, p. 1140, last display

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_NonmonotoneSubmod_Nonadaptive_omega

namespace NonmonotoneSubmod.Nonadaptive

/-- Theorem 2.6 (Feige–Mirrokni–Vondrák 2011, p. 1139), in the explicit form of its proof
(p. 1140, last display). Let `f` be nonnegative and submodular on a nonempty ground set of
`n` elements. Let `ω̃` be any estimates with `|ω̃(x) − ω(x)| < OPT/n²` for all `x`, and
`A = {x : ω̃(x) > 0}`. Then the expected value of Algorithm NA, which returns `R = X(1/2)`
with probability 8/9 and `A` with probability 1/9, satisfies
`(8/9) E[f(X(1/2))] + (1/9) f(A) ≥ (1/3 − 4/(9n)) OPT`. -/
theorem nonadaptive_one_third {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (ωt : X → ℝ)
    (hωt : ∀ x, |ωt x - omega f x| < NonmonotoneSubmod.Shared.OPT f / (Fintype.card X : ℝ) ^ 2) :
    (1 / 3 - 4 / (9 * (Fintype.card X : ℝ))) * NonmonotoneSubmod.Shared.OPT f ≤
      (8 / 9) * NonmonotoneSubmod.Shared.F f (fun _ => 1 / 2) + (1 / 9) * f (Finset.univ.filter (fun x => 0 < ωt x)) := by sorry

end NonmonotoneSubmod.Nonadaptive
