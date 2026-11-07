-- Prove2me | Theorems.Thm_LocalBreadth_lemma_5_22
-- name    : LocalBreadth.lemma_5_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:55.30961+00:00
-- url     : https://prove2.me/theorems/c55e383f-2d1d-4b9b-9600-e857e5820366
-- title:
--   Lemma 5.22 — the density bound at each accuracy copy
-- statement:
--   Let $\mathcal X$ be a nonempty countable family of infinite subsets of $\mathbb Z$.
--   In the protected forest, fix a tie-breaking rule, $K\in\mathcal X$, a full enumeration of $K$, and $m\ge1$. The output set $O$ of the formal-copy algorithm satisfies
--   $$d_{\mathrm{banach}}(O,K)\ge q_{K,m}=(b(K)-2^{-m})_+.$$
--
--   Differences from the source:
--   - encoding: "the construction" of the forest, with free choices → every term of the structure `ProtectedForest`; reason: each step of the recursion is a field, so a term is exactly one outcome of the construction
--   - encoding: $z_m=(K,m)$ → a vertex $z$ with `F.L z = K`, with $m$ read as `F.m z`; reason: same vertices
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Lemma 5.22, p.41

import Mathlib
import Definitions.Def_LocalBreadth_dBanach
import Definitions.Def_LocalBreadth_ProtectedForest
import Definitions.Def_LocalBreadth_genOf

namespace LocalBreadth

/-- Lemma 5.22. Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…), p.41. Fix `m ≥ 1`. The
output set `O` of the formal-copy algorithm satisfies `d_banach(O, K) ≥ q_{K,m} = (b(K) − 2^{−m})⁺`.

**Formalization Note.** The copy `(K, m)` is the vertex `z` with `F.L z = K` and `F.m z = m`; `F.q z` is
`(b(K) − 2^{−m})⁺` by definition. -/
theorem lemma_5_22 (X : Set (Set ℤ)) (hne : X.Nonempty) (hc : X.Countable) (hinf : ∀ L ∈ X, L.Infinite)
    (F : ProtectedForest X) (pick : Set ℤ → ℤ) (hpick : ∀ S : Set ℤ, S.Nonempty → pick S ∈ S)
    (K : Set ℤ) (hK : K ∈ X) (x : ℕ → ℤ) (hx : IsFullEnumeration K x)
    (z : ℕ) (hz : F.L z = K) :
    F.q z ≤ dBanach (outputSet (genOf F.L F.parent F.board pick) x) K := by sorry

end LocalBreadth
