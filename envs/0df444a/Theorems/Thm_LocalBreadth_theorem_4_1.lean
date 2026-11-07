-- Prove2me | Theorems.Thm_LocalBreadth_theorem_4_1
-- name    : LocalBreadth.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:55:27.976995+00:00
-- url     : https://prove2.me/theorems/4568c52c-c9cb-4d3d-bacf-49044ca7635d
-- title:
--   Theorem 4.1 — the upper bound
-- statement:
--   Let $\mathcal X$ be a nonempty countable family of infinite subsets of $\mathbb Z$.
--   Let $G$ be a fresh generator that is eventually valid on every full enumeration of every language in $\mathcal X$. Then for every $K\in\mathcal X$ there is a full enumeration of $K$ such that the output set $O$ of $G$ satisfies
--   $$d_{\mathrm{banach}}(O,K)\le b(K).$$
--
--   Differences from the source:
--   - encoding: a generator producing $o_t$ after receiving $x_t$, for $t\ge1$ → a function `List ℤ → ℤ` of the inputs so far, with time 0-indexed; reason: the generator is deterministic and unrestricted (pp.1, 16), so its outputs are determined by the inputs; same runs
--   - generalization: global freshness $o_t\notin S_t\cup O_{t-1}$ for every $t$ (p.13) → `IsFresh X G`, required only on full enumerations of members of $\mathcal X$; reason: this weakens the hypothesis on the generator, so the upper bound covers every globally fresh generator as well; the adversary only ever plays inside languages of $\mathcal X$
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Theorem 4.1, p.19

import Mathlib
import Definitions.Def_LocalBreadth_Generator
import Definitions.Def_LocalBreadth_dBanach
import Definitions.Def_LocalBreadth_bComb

namespace LocalBreadth

/-- Theorem 4.1. Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…), p.19. For a fresh
generator eventually valid on every full enumeration of every language in `X`, and every `K ∈ X`, there is
a full enumeration of `K` with `d_banach(O, K) ≤ b(K)`. -/
theorem theorem_4_1 (X : Set (Set ℤ)) (hne : X.Nonempty) (hc : X.Countable) (hinf : ∀ L ∈ X, L.Infinite)
    (G : Generator) (hfresh : IsFresh X G) (hvalid : IsEventuallyValid X G) :
    ∀ K ∈ X, ∃ x, IsFullEnumeration K x ∧ dBanach (outputSet G x) K ≤ b X K := by sorry

end LocalBreadth
