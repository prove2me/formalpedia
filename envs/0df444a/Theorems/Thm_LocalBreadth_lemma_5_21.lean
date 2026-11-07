-- Prove2me | Theorems.Thm_LocalBreadth_lemma_5_21
-- name    : LocalBreadth.lemma_5_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:57.681801+00:00
-- url     : https://prove2.me/theorems/17c869b9-72a4-4a1b-9e31-3b12e4b1098b
-- title:
--   Lemma 5.21 — the guess is eventually captured below every copy of the target
-- statement:
--   Let $\mathcal X$ be a nonempty countable family of infinite subsets of $\mathbb Z$.
--   In the protected forest, fix $K\in\mathcal X$, a full enumeration of $K$, and a formal copy $z$ of $K$. After some finite time, every current guess $Q_t$ is defined and lies in the subtree rooted at $z$, including $z$ itself.
--
--   Differences from the source:
--   - encoding: "the construction" of the forest, with free choices → every term of the structure `ProtectedForest`; reason: each step of the recursion is a field, so a term is exactly one outcome of the construction
--   - encoding: $z_m=(K,m)$ → a vertex $z$ with `F.L z = K`, with $m$ read as `F.m z`; reason: same vertices
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Lemma 5.21, p.39

import Mathlib
import Definitions.Def_LocalBreadth_ProtectedForest
import Definitions.Def_LocalBreadth_genOf

namespace LocalBreadth

/-- Lemma 5.21. Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…), p.39. On a full
enumeration of `K ∈ X`, for a formal copy `z` of `K`: after some finite time, every current guess `Q_t` is
defined and lies in the subtree rooted at `z`. The paper's single-copy form is Lemma 5.16, p.35.

**Formalization Note.** A copy `z_m = (K, m)` is a vertex with `F.L z = K`. The guess does not depend on the
tie-breaking rule. -/
theorem lemma_5_21 (X : Set (Set ℤ)) (hne : X.Nonempty) (hc : X.Countable) (hinf : ∀ L ∈ X, L.Infinite)
    (F : ProtectedForest X) (K : Set ℤ) (hK : K ∈ X) (x : ℕ → ℤ) (hx : IsFullEnumeration K x)
    (z : ℕ) (hz : F.L z = K) :
    ∃ t₀, ∀ t ≥ t₀, ∃ Q, guess F.L (inputsUpTo x t) = some Q ∧ IsAnc F.parent z Q := by sorry

end LocalBreadth
