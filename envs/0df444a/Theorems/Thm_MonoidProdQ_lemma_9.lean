-- Prove2me | Theorems.Thm_MonoidProdQ_lemma_9
-- name    : MonoidProdQ.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:45:20.043209+00:00
-- url     : https://prove2.me/theorems/12ce3581-b4e1-43c9-b20d-fca66cf95d9e
-- title:
--   Lemma 9 (Sandwich Lemma): $pqr=q$ implies $q=pq$ and $q=qr$
-- statement:
--   Let $M$ be a finite aperiodic monoid, not necessarily commutative, and let $p,q,r\in M$. If
--
--   $$pqr=q,$$
--
--   then $q=pq$ and $q=qr$.
--
--   This is the basic consequence of aperiodicity used throughout the paper: an element that is unchanged when sandwiched is already absorbed on each side separately. It is the key step in Proposition 19.
--
--   Differences from the source: none.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Lemma 9 (Sandwich Lemma), p.23

import Definitions.Def_MonoidProdQ_IsAperiodic

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Lemma 9 (Sandwich Lemma), p.23: "Let M be a finite aperiodic monoid. If pqr = q then
q = pq and q = qr." `M` need not be commutative. -/
theorem lemma_9 {M : Type*} [Monoid M] [Finite M] (hM : IsAperiodic M) {p q r : M}
    (h : p * q * r = q) : q = p * q ∧ q = q * r := by sorry

end MonoidProdQ
