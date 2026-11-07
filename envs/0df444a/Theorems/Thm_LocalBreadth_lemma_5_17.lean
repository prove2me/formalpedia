-- Prove2me | Theorems.Thm_LocalBreadth_lemma_5_17
-- name    : LocalBreadth.lemma_5_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:49.875969+00:00
-- url     : https://prove2.me/theorems/36ed9d4c-ca02-4558-925a-9bd5a582d5b1
-- title:
--   Lemma 5.17 — every output is available, and the algorithm is eventually valid
-- statement:
--   Let $\mathcal X$ be a nonempty countable family of infinite subsets of $\mathbb Z$.
--   In the protected forest, for any tie-breaking rule choosing inside nonempty sets, the online algorithm is fresh on $\mathcal X$, and on every full enumeration of every $K\in\mathcal X$ it produces only finitely many outputs outside $K$.
--
--   Differences from the source:
--   - encoding: "the construction" of the forest, with free choices → every term of the structure `ProtectedForest`; reason: each step of the recursion is a field, so a term is exactly one outcome of the construction
--   - reading: the numbered statement for the fixed-error forest of §§5.4–5.7 → the statement for the formal-copy forest of §5.8; reason: §5.8 states that these results apply with formal copies and compressed chains, and the goal needs that form
--   - reading: Lemma 5.17 says only "finitely many outputs outside $K$" → freshness is a clause of the same theorem; reason: the page proves availability in the paragraph completing Theorem 5.1, with no number of its own, and both clauses are needed for the goal
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Lemma 5.17, p.36; completion of the proof of Theorem 5.1, p.37; §5.8.8, p.40

import Mathlib
import Definitions.Def_LocalBreadth_ProtectedForest
import Definitions.Def_LocalBreadth_genOf

namespace LocalBreadth

/-- Lemma 5.17. Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…), p.36, with §5.8.8,
p.40: the generator produces only finitely many outputs outside `K`, on every full enumeration of every
`K ∈ X`, whatever the forest and the tie-breaking. Also every output is available ("Completion of the
proof of Theorem 5.1", p.37). -/
theorem lemma_5_17 (X : Set (Set ℤ)) (hne : X.Nonempty) (hc : X.Countable) (hinf : ∀ L ∈ X, L.Infinite)
    (F : ProtectedForest X) (pick : Set ℤ → ℤ) (hpick : ∀ S : Set ℤ, S.Nonempty → pick S ∈ S) :
    IsFresh X (genOf F.L F.parent F.board pick) ∧
    IsEventuallyValid X (genOf F.L F.parent F.board pick) := by sorry

end LocalBreadth
