-- Prove2me | Theorems.Thm_LocalBreadth_theorem_5_23
-- name    : LocalBreadth.theorem_5_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:55:35.188052+00:00
-- url     : https://prove2.me/theorems/e2d8ab54-3c7c-40a5-b4ed-671dd71151d4
-- title:
--   Theorem 5.23 — the lower bound
-- statement:
--   Let $\mathcal X$ be a nonempty countable family of infinite subsets of $\mathbb Z$.
--   There is one generator, with every output available, that is eventually valid on every full enumeration of every language of $\mathcal X$ and whose output set satisfies $d_{\mathrm{banach}}(O,K)\ge b(K)$ for every target $K\in\mathcal X$ and every full enumeration of $K$.
--
--   Differences from the source:
--   - encoding: a generator producing $o_t$ after receiving $x_t$, for $t\ge1$ → a function `List ℤ → ℤ` of the inputs so far, with time 0-indexed; reason: the generator is deterministic and unrestricted (pp.1, 16), so its outputs are determined by the inputs; same runs
--   - reading: Theorem 5.23 does not repeat the availability of outputs → `IsFresh` is a clause of the existence; reason: freshness is the standing convention of p.13, and Theorem 2.5 states it for this generator
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Theorem 5.23, p.41; "every output is available", Theorem 2.5, p.16

import Mathlib
import Definitions.Def_LocalBreadth_Generator
import Definitions.Def_LocalBreadth_dBanach
import Definitions.Def_LocalBreadth_bComb

namespace LocalBreadth

/-- Theorem 5.23. Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…), p.41. For every
nonempty countable class `X` of infinite subsets of `ℤ`, there is one generator, with every output available,
that is eventually valid on every full enumeration and whose output set satisfies `d_banach(O, K) ≥ b(K)`
for every target `K ∈ X`. -/
theorem theorem_5_23 (X : Set (Set ℤ)) (hne : X.Nonempty) (hc : X.Countable) (hinf : ∀ L ∈ X, L.Infinite) :
    ∃ G : Generator, IsFresh X G ∧ IsEventuallyValid X G ∧
      ∀ K ∈ X, ∀ x, IsFullEnumeration K x → b X K ≤ dBanach (outputSet G x) K := by sorry

end LocalBreadth
