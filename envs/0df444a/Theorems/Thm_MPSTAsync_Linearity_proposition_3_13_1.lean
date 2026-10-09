-- Prove2me | Theorems.Thm_MPSTAsync_Linearity_proposition_3_13_1
-- name    : MPSTAsync.Linearity.proposition_3_13_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:07:55.240473+00:00
-- url     : https://prove2.me/theorems/59ce54d4-c808-48f6-a70b-124941f124b1
-- title:
--   Proposition 3.13(1), p. 20 — one-time unfolding characterizes linearity of every positive unfolding
-- statement:
--   Let $G$ be a well-formed global type, and let $n\ge1$. Its one-time unfolding is linear if and only if its $n$-th finite unfolding is linear:
--
--   $$
--   \operatorname{Linear}(G^{(1)})\iff\operatorname{Linear}(G^{(n)}).
--   $$
--
--   Consequently, the linearity condition on the finitely unfolded syntax stabilizes after one unfolding. This is Proposition 3.13(1), the paper's basis for its subsequent decidability statement.
--
--   **Formalization Note** `WellFormed G` makes explicit the paper's standing guarded-recursion and closed carried-type conventions, together with its stated shape conventions. Appendix A explicitly takes $n\ge1$; the zero case fails for its examples. Unfolding does not enter carried types, while `Linear` checks them recursively. The statement assumes no folding lemma or dependency chain as a hypothesis.
-- source:
--   Honda, Yoshida, Carbone, Multiparty Asynchronous Session Types, J. ACM 63(1) (2016), Art. 9, p. 20, Proposition 3.13(1), Appendix A pp. 52–53; https://doi.org/10.1145/2827695

import Mathlib
import Definitions.Def_MPSTAsync_Linearity_Linearity

namespace MPSTAsync.Linearity

theorem proposition_3_13_1 (G : GType) (hG : WellFormed G) (n : ℕ) (hn : 1 ≤ n) :
    Linear (unfold 1 G) ↔ Linear (unfold n G) := by sorry

end MPSTAsync.Linearity
