-- Prove2me | Theorems.Thm_LocalBreadth_corollary_5_19
-- name    : LocalBreadth.corollary_5_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:29.569266+00:00
-- url     : https://prove2.me/theorems/15f2e262-33ff-419a-8038-b417deb516d5
-- title:
--   Corollary 5.19 — density on regular boards
-- statement:
--   Let $\mathcal X$ be a nonempty countable family of infinite subsets of $\mathbb Z$.
--   In the protected forest, fix a tie-breaking rule, $K\in\mathcal X$, a full enumeration of $K$, a formal copy $z$ of $K$, and a capture time $t_0$: for all $t\ge t_0$, $Q_t$ is defined and lies in the subtree rooted at $z$. Then only finitely many $z$-boards are exceptional, and every regular $z$-board $I$ satisfies
--   $$|O\cap K\cap I|\ge q_z\,|K\cap I|.$$
--
--   Differences from the source:
--   - encoding: "the construction" of the forest, with free choices → every term of the structure `ProtectedForest`; reason: each step of the recursion is a field, so a term is exactly one outcome of the construction
--   - reading: the numbered statement for the fixed-error forest of §§5.4–5.7 → the statement for the formal-copy forest of §5.8; reason: §5.8 states that these results apply with formal copies and compressed chains, and the goal needs that form
--   - encoding: $z_m=(K,m)$ → a vertex $z$ with `F.L z = K`, with $m$ read as `F.m z`; reason: same vertices
--   - reading: "There are finitely many such boards" in the paragraph defining exceptional boards → the finiteness is a clause of this theorem; reason: both are needed for Lemma 5.22 and the page has no separate number for the finiteness
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Corollary 5.19, p.36; exceptional boards, p.35; §5.8.9, p.41

import Mathlib
import Definitions.Def_LocalBreadth_ProtectedForest
import Definitions.Def_LocalBreadth_genOf

namespace LocalBreadth

/-- Corollary 5.19. Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…), p.36, with the
exceptional boards of p.35 and §5.8.9, p.41. Fix a copy `z` of `K` and a capture time `t₀`, after which every
guess lies in the subtree of `z`. There are finitely many exceptional `z`-boards, and every regular `z`-board
`I` satisfies `|O ∩ K ∩ I| ≥ q_z |K ∩ I|`. -/
theorem corollary_5_19 (X : Set (Set ℤ)) (hne : X.Nonempty) (hc : X.Countable) (hinf : ∀ L ∈ X, L.Infinite)
    (F : ProtectedForest X) (pick : Set ℤ → ℤ) (hpick : ∀ S : Set ℤ, S.Nonempty → pick S ∈ S)
    (K : Set ℤ) (hK : K ∈ X) (x : ℕ → ℤ) (hx : IsFullEnumeration K x)
    (z : ℕ) (hz : F.L z = K) (t₀ : ℕ)
    (hcapture : ∀ t ≥ t₀, ∃ Q, guess F.L (inputsUpTo x t) = some Q ∧ IsAnc F.parent z Q) :
    {I | (∃ w, I = F.board z w) ∧ IsExceptional F.L F.parent F.board pick x z t₀ I}.Finite ∧
    ∀ w, ¬ IsExceptional F.L F.parent F.board pick x z t₀ (F.board z w) →
      F.q z * ((K ∩ F.board z w).ncard : ℝ) ≤
        ((outputSet (genOf F.L F.parent F.board pick) x ∩ K ∩ F.board z w).ncard : ℝ) := by sorry

end LocalBreadth
