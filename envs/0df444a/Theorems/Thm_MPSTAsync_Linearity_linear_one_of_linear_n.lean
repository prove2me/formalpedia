-- Prove2me | Theorems.Thm_MPSTAsync_Linearity_linear_one_of_linear_n
-- name    : MPSTAsync.Linearity.linear_one_of_linear_n
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:07:37.667443+00:00
-- url     : https://prove2.me/theorems/3768bded-a237-4571-b7d2-49feec599c02
-- title:
--   Proof of Proposition 3.13(1), p. 20 — linearity of an n-th unfolding implies linearity after one unfolding
-- statement:
--   Let $G$ be a well-formed global type and let $n\ge1$. If its $n$-th finite unfolding is linear, then its one-time unfolding is linear:
--
--   $$
--   \operatorname{Linear}(G^{(n)})\Longrightarrow\operatorname{Linear}(G^{(1)}).
--   $$
--
--   This is the reverse direction singled out in the proof of Proposition 3.13(1), and it makes the finite one-time test a necessary condition for linearity at every later unfolding.
--
--   **Formalization Note** `WellFormed G` makes explicit the paper's standing guarded-recursion and closed carried-type conventions, together with its stated shape conventions. Unfolding does not enter carried types. The lower bound $n\ge1$ is taken from Appendix A's induction and excludes the paper's zero-unfolding counterexample. The statement uses no hypothesis about folding or dependency chains.
-- source:
--   Honda, Yoshida, Carbone, Multiparty Asynchronous Session Types, J. ACM 63(1) (2016), Art. 9, p. 20, proof of Proposition 3.13(1); https://doi.org/10.1145/2827695

import Mathlib
import Definitions.Def_MPSTAsync_Linearity_Linearity

namespace MPSTAsync.Linearity

theorem linear_one_of_linear_n (G : GType) (hG : WellFormed G) (n : ℕ) (hn : 1 ≤ n) :
    Linear (unfold n G) → Linear (unfold 1 G) := by sorry

end MPSTAsync.Linearity
