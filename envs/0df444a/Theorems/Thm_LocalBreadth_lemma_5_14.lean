-- Prove2me | Theorems.Thm_LocalBreadth_lemma_5_14
-- name    : LocalBreadth.lemma_5_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:35.731312+00:00
-- url     : https://prove2.me/theorems/719a60be-7ede-4f12-8341-9ef5f1d88e40
-- title:
--   Lemma 5.14 — the uniform board bound
-- statement:
--   Let $\mathcal X$ be a nonempty countable family of infinite subsets of $\mathbb Z$.
--   In the protected forest, for every $a\preceq v$ and every $a$-board $I$,
--   $$p(\overline H[a,v],L_a\cap I)\ge\max\{0,\,s_a-1/N_a\}\ge q_a.$$
--
--   The bound is uniform over all forest paths and all boards, including those near the origin, which is what a density guarantee needs.
--
--   Differences from the source:
--   - encoding: "the construction" of the forest, with free choices → every term of the structure `ProtectedForest`; reason: each step of the recursion is a field, so a term is exactly one outcome of the construction
--   - reading: the numbered statement for the fixed-error forest of §§5.4–5.7 → the statement for the formal-copy forest of §5.8; reason: §5.8 states that these results apply with formal copies and compressed chains, and the goal needs that form
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Lemma 5.14, eq. (22), p.34; §5.8.7, p.40

import Mathlib
import Definitions.Def_LocalBreadth_ProtectedForest

namespace LocalBreadth

/-- Lemma 5.14 (Uniform board bound). Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…),
eq. (22), p.34, with §5.8.7, p.40. For every `a ⪯ v` and every `a`-board `I`,
`p(H[a, v], L_a ∩ I) ≥ max{0, s_a − 1/N_a} ≥ q_a`. -/
theorem lemma_5_14 (X : Set (Set ℤ)) (hne : X.Nonempty) (hc : X.Countable) (hinf : ∀ L ∈ X, L.Infinite)
    (F : ProtectedForest X) (a v : ℕ) (hav : IsAnc F.parent a v) (w : ℤ) :
    max 0 (F.s a - 1 / (F.N a : ℝ)) ≤ pScore (chainFrom F.L F.parent a v) (F.L a ∩ F.board a w) ∧
    F.q a ≤ max 0 (F.s a - 1 / (F.N a : ℝ)) := by sorry

end LocalBreadth
