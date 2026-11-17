-- Prove2me | Theorems.Thm_LocalBreadth_Supplement_theorem_5_1
-- name    : LocalBreadth.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:24:00.464603+00:00
-- url     : https://prove2.me/theorems/8715a8d3-a827-4a57-b64f-a9c0ee04cd3a
-- title:
--   Theorem 5.1 — fixed-error lower bound $d_{\mathrm{banach}}(O,K)\ge(b(K)-\varepsilon)_+$
-- statement:
--   Let $\mathcal X$ be a nonempty countable family of infinite subsets of $\mathbb Z$, and let $b(K)$ be the structural value of the mission (eq. (9)). For every $\varepsilon>0$ there is one generator $\mathcal A_\varepsilon$, fresh on $\mathcal X$, such that on every full enumeration of every $K\in\mathcal X$:
--   1. all but finitely many outputs belong to $K$; and
--   2. the output set $O$ satisfies
--   $$d_{\mathrm{banach}}(O,K)\ge\big(b(K)-\varepsilon\big)_+,\qquad x_+=\max\{x,0\}.$$
--
--   This is the fixed-error version of the lower bound of Theorem 1.5: the generator may depend on $\varepsilon$ but not on the target or the enumeration.
--
--   Differences from the source:
--   - reading: one generator A_ε with (1) eventual validity and (2) the density bound → ∃ G, IsFresh X G ∧ IsEventuallyValid X G ∧ the density bound; reason: the model conventions (p.13) require the global freshness condition of every generator throughout the paper
--   - encoding: time t = 1, 2, … with inputs x_t, outputs o_t → 0-indexed time; the output at time t is G applied to x 0, …, x t; reason: index shift only; the same runs
--   - encoding: b(K) = lim_{n→∞} b_n(K) → the published b X K = ⨆ n, bComb X (n+1) K; reason: b_n increases with n, so the limit is this supremum; the published goal LocalBreadth.theorem_1_5 states that b_n(K) → b X K
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc309339291b1a61b8504342f4050ece6e4e903dd18b2bf541446f1064), §5.2, Theorem 5.1, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_LocalBreadth_Generator
import Definitions.Def_LocalBreadth_dBanach
import Definitions.Def_LocalBreadth_bComb

namespace LocalBreadth.Supplement

/-- Theorem 5.1 (fixed-error lower bound). Kleinberg, Wei, STOC 2027 submission (manuscript sha256
f924cbfc…), §5.2, p.23. Let `X` be a nonempty countable family of infinite subsets of `ℤ`. For every
`ε > 0` there is one generator `A_ε` such that, on every full enumeration of every `K ∈ X`, all but
finitely many outputs belong to `K`, and the output set satisfies `d_banach(O, K) ≥ (b(K) - ε)_+`.

**Formalization Note.** The standing family of Part I (p.13) is a hypothesis. The generator also
satisfies the global freshness condition required of every generator throughout the paper (p.13).
The generator may depend on `ε`, not on `K` or the enumeration. -/
theorem theorem_5_1 (X : Set (Set ℤ)) (hne : X.Nonempty) (hc : X.Countable)
    (hinf : ∀ L ∈ X, L.Infinite) (ε : ℝ) (hε : 0 < ε) :
    ∃ G : Generator, IsFresh X G ∧ IsEventuallyValid X G ∧
      ∀ K ∈ X, ∀ x, IsFullEnumeration K x → max (b X K - ε) 0 ≤ dBanach (outputSet G x) K := by sorry

end LocalBreadth.Supplement
