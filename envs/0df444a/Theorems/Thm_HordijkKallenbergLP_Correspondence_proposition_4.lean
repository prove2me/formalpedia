-- Prove2me | Theorems.Thm_HordijkKallenbergLP_Correspondence_proposition_4
-- name    : HordijkKallenbergLP.Correspondence.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:31.393976+00:00
-- url     : https://prove2.me/theorems/69d97afa-6099-444c-9d92-04bb523f26e1
-- title:
--   Proposition 4 — equalities on supported actions
-- statement:
--   Fix positive normalized state weights $\beta$, an optimal dual solution $(x,y)$ and an optimal primal solution $(\phi,u)$. Let $\overline A(i)$ be the actions with $\pi_{ia}(x,y)>0$. For every $a\in\overline A(i)$,
--
--   $$\phi_i=\sum_jp_{iaj}\phi_j;\qquad i\in E_x\implies\phi_i+u_i=r_{ia}+\sum_jp_{iaj}u_j.$$
--
--   These equalities identify which superharmonic constraints become tight on the actions used by an optimal dual point. **Formalization Note** The primal first component is any optimal $\phi$; its identification with the optimal gain follows from Theorem 6 and positive $\beta$, rather than being added as an assumption.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, pp. 360–361, Proposition 4

import Mathlib
import Definitions.Def_HordijkKallenbergLP_Correspondence_Model

namespace HordijkKallenbergLP.Correspondence

open MarkovDecisionProcesses

/-- Hordijk and Kallenberg (1979), Proposition 4, pp. 360–361.
The complementary-slackness identities hold for every action given positive
probability by the policy of any optimal dual solution. -/
theorem proposition_4 {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [DecidableEq A] [Nonempty S]
    (M : StationaryMDP S A) (β : S → ℝ)
    (hβpos : ∀ i, 0 < β i) (hβsum : ∑ i, β i = 1)
    (x y : HordijkKallenbergLP.SingleLP.Pair M → ℝ) (hxy : DualOptimal M β x y)
    (φ u : S → ℝ) (hφu : PrimalOptimal M β φ u) :
    ∀ i a, 0 < dualPolicyWeight M x y i a →
      (∑ j, M.trans i a j * φ j = φ i) ∧
      (i ∈ Ex M x → φ i + u i = M.reward i a + ∑ j, M.trans i a j * u j) := by sorry

end HordijkKallenbergLP.Correspondence
