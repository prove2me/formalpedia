-- Prove2me | Theorems.Thm_OAI_RealDeligneDrinfeld_BraidInsertionSum_pentagon
-- name    : OAI.RealDeligneDrinfeld.BraidInsertionSum.pentagon
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T18:45:36.130237+00:00
-- url     : https://prove2.me/theorems/83432f0c-2dfe-4e5d-a37b-0e6986c1be9e
-- title:
--   Section 6 over ℝ (OpenAI, Deligne–Drinfeld) — exponentials of solution derivations preserve the pentagon identity in the truncated braid algebra
-- statement:
--   Let $I$ be a type, $N \in \mathbb N$, $s \subseteq I$ a finite set, and for each $i \in I$ let $q_i \in W_{\mathbb R}$ be a real solution of the defining equations, homogeneous of weight $n_i > 2$ (`OAI.RealDeligneDrinfeld.W`, `Ln`). Let $Q$ be OpenAI's truncated real free cutoff algebra (`FreeCutoffCategory.Q N`), and let $\mathrm{IAB}, \mathrm{IAD}, \mathrm{IDE}, \mathrm{IBC}, \mathrm{ICE}$ be the five algebra maps from it to the truncated real braid algebra that substitute for $(x, y)$ the five pairs of the pentagon equation, $(t_{01}, t_{12})$, $(t_{02} + t_{12}, t_{23})$, $(t_{01}, t_{12} + t_{13})$, $(t_{01} + t_{02}, t_{13} + t_{23})$ and $(t_{12}, t_{23})$ respectively (`BraidInsertionExp`). If $a \in Q$ satisfies
--
--   $$\mathrm{IDE}(a)\,\mathrm{IAD}(a) = \mathrm{ICE}(a)\,\mathrm{IBC}(a)\,\mathrm{IAB}(a),$$
--
--   then so does $a' = \exp\bigl(\sum_{i \in s} \Delta_{q_i}\bigr)(a)$, where $\Delta_q$ is OpenAI's gauged derivation of the free cutoff category attached to $q$, on the arrows from object $0$ to object $1$, and $\exp$ is the exponential of a nilpotent operator (`CategoryExp.act (BraidInsertionSum.free N s q n hqn) 0 1 a`).
--
--   OpenAI, *The Deligne–Drinfeld conjecture* (September 23, 2026), §6 (“A rational Lie algebra of categorical values”, pp. 27–31): the solutions act on the parenthesized-chord categories by compatible derivations, and their values $\delta(\alpha)$ form the subspace $V \subseteq W$ (Proposition 6.1, p. 28). This statement is OpenAI's Lean theorem `OAI.RealDeligneDrinfeld.BraidInsertionSum.pentagon` (`lean/OAI/Algebra/Drinfeld`, Apache-2.0), the compatibility of those derivations, exponentiated, with the five insertions into four strands, in the real form used for the holonomy values of §7. All objects are OpenAI's, from the bundles `Def_DeligneDrinfeldInternals` and `Def_DeligneDrinfeldBraid`. Published as one of the intermediate statements through which the proof of `OAI.DeligneDrinfeld.main` is checked in pieces.
-- source:
--   OpenAI, The Deligne–Drinfeld conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf, Section 6, pp. 27-31, in the real form used in Section 7; Lean: https://github.com/openai/math/tree/main/lean/OAI/Algebra/Drinfeld (Apache-2.0)

import Mathlib
import Definitions.Def_DeligneDrinfeldBraid

namespace OAI.RealDeligneDrinfeld.BraidInsertionSum

theorem pentagon {I : Type*} (N : ℕ) (s : Finset I)
    (q : I → OAI.RealDeligneDrinfeld.L) (n : I → ℕ) (hq : ∀ (i : I), q i ∈ OAI.RealDeligneDrinfeld.W)
    (hqn : ∀ (i : I), q i ∈ OAI.RealDeligneDrinfeld.Ln (n i)) (hn : ∀ (i : I), 2 < n i)
    (a : OAI.RealDeligneDrinfeld.FreeCutoffCategory.Q N)
    (ha :
      (OAI.RealDeligneDrinfeld.BraidInsertionExp.IDE N) a * (OAI.RealDeligneDrinfeld.BraidInsertionExp.IAD N) a =
        (OAI.RealDeligneDrinfeld.BraidInsertionExp.ICE N) a * (OAI.RealDeligneDrinfeld.BraidInsertionExp.IBC N) a *
          (OAI.RealDeligneDrinfeld.BraidInsertionExp.IAB N) a) :
    let a' := (OAI.DeligneDrinfeld.CategoryExp.act (OAI.RealDeligneDrinfeld.BraidInsertionSum.free N s q n hqn) 0 1) a;
    (OAI.RealDeligneDrinfeld.BraidInsertionExp.IDE N) a' * (OAI.RealDeligneDrinfeld.BraidInsertionExp.IAD N) a' =
      (OAI.RealDeligneDrinfeld.BraidInsertionExp.ICE N) a' * (OAI.RealDeligneDrinfeld.BraidInsertionExp.IBC N) a' *
        (OAI.RealDeligneDrinfeld.BraidInsertionExp.IAB N) a' := by
  sorry

end OAI.RealDeligneDrinfeld.BraidInsertionSum
