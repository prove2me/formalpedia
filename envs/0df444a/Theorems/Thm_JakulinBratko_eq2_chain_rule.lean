-- Prove2me | Theorems.Thm_JakulinBratko_eq2_chain_rule
-- name    : JakulinBratko.eq2_chain_rule
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:02:34.982727+00:00
-- url     : https://prove2.me/theorems/2acca6b0-1f90-4846-be35-4a3629d2a3a5
-- title:
--   Eq. (2) — $H(R\mid Y)=H(R,Y)-H(Y)$
-- statement:
--   Let $P$ be a joint law and let $R,Y$ be disjoint sets of attributes. The conditional entropy, given by its defining sum, satisfies
--
--   $$
--   H(R\mid Y)=H(R\cup Y)-H(Y).
--   $$
--
--   This is the identity that turns every sum form of the mission into a combination of joint entropies.
--
--   Differences from the source:
--   - generalization: single attributes A, B → disjoint Finsets R, Y of attributes; reason: the paper itself uses groups (I(A, B; C) in Eq. (5)); singletons give the printed display
--   - encoding: P(a|b) → the quotient P(z) / P(z|_Y) with Real.logb 2; reason: Lean convention; the two agree wherever P(z) > 0 and all other terms have weight 0
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.2, Eq. (2), p.4

import Definitions.Def_JakulinBratko_IsLaw
import Definitions.Def_JakulinBratko_H
import Definitions.Def_JakulinBratko_condEntSum

namespace JakulinBratko

/-- Eq. (2), p.4 (Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3), for disjoint groups of attributes: the conditional entropy
`H(R | Y)`, given by its defining sum, equals `H(R, Y) - H(Y)`. -/
theorem eq2_chain_rule {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (hP : IsLaw P)
    (R Y : Finset ι) (hRY : Disjoint R Y) :
    condEntSum P R Y = H P (R ∪ Y) - H P Y := by sorry

end JakulinBratko
