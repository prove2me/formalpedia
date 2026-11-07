-- Prove2me | Theorems.Thm_HDXConc_theorem_2_3
-- name    : HDXConc.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:00:09.021628+00:00
-- url     : https://prove2.me/theorems/a0453704-f664-431a-9cab-fe7dfac75b2c
-- title:
--   Theorem 2.3, p.13 — Trickle Down Theorem [Opp18], $\mu=\lambda/(1-(d-2)\lambda)$
-- statement:
--   Let $X$ be a pure $d$-dimensional complex, $d\ge2$, with top density $\pi_d$, such that the underlying graph of the link of every face with at most $d-2$ vertices is connected. Suppose that for every $s\in X(d-2)$ the link $X_s$ has second walk eigenvalue at most $\lambda$, where $\lambda<\frac1{d-1}$. Then for every face $s$ with at most $d-2$ vertices, including $s=\emptyset$,
--
--   $$\lambda(X_s)\le\mu,\qquad\text{where }\mu=\frac{\lambda}{1-(d-2)\lambda}.$$
--
--   Thus spectral bounds on the top links alone control the whole complex, up to the threshold $\frac1{d-1}$. The paper cites this theorem from [Opp18].
--
--   Differences from the source:
--   - reading: "the underlying graph of every link is connected" → connectivity for every s ∈ X with s.card + 2 ≤ d, including ∅; reason: read over all faces it would require the edgeless links of (d−1)-faces to be connected, excluding the complete complex and the paper's own example on p.18; footnote 2 and the only use (Theorem 2.3) concern these links, and this reading is the weaker hypothesis, so the theorem is the stronger one
--   - generalization: λ < 1/(d−1), with Definition 2.1 written for λ ∈ (0, 1) → every real lam < 1/(d−1), including negative values and zero; reason: the theorem as printed has no sign condition; the printed positive case is an instance
--   - encoding: λ(X_s) ≤ λ, the second eigenvalue of the walk with weights π^s_2 → SecondEigLE (linkVerts X s) (linkWeight X d π s) λ, the Rayleigh quotient bound on the degree-orthogonal complement of the constants, with weights equal to π^s_2 up to a constant per link; reason: Courant–Fischer gives the equivalence, and a constant factor does not change the walk
--   - encoding: X is a µ-local spectral expander (Definition 2.1: every s ∈ X^{≤d−2}) → ∀ s ∈ X with s.card + 2 ≤ d, SecondEigLE at µ; reason: this is the definition spelled out; X^{≤d−2} includes ∅
--   - encoding: a d-dimensional (pure) complex, with co-dimension 2 links and d − 1 in denominators → 2 ≤ d and SteurerHDX.IsPure X d, with X a Finset (Finset V) over a finite type V; reason: this is the domain the statement is written for; dimension is the number of vertices, as in the paper, and the top density rules out the empty collection
--   - encoding: π_d : X(d) → (0, 1] a probability density → π : Finset V → ℝ, positive on X(d) with total mass 1 there, never read elsewhere; reason: the bound by 1 follows, and values off X(d) do not occur
-- source:
--   Das, Hopkins, Ray, Tung, Concentration on HDX: Simplified and Optimized, STOC 2027 submission (manuscript sha256 ea5bee5f…), Theorem 2.3, p.13; Definition 2.1, p.13

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_HDXConc_IsTopDensity
import Definitions.Def_HDXConc_IsTopLinkExpander

namespace HDXConc

/-- Theorem 2.3 (Trickle Down Theorem [Opp18]), p.13: if the underlying graph of every link is connected and for every
`s ∈ X(d - 2)` the link `X_s` is a one-sided `lam`-expander with `lam < 1 / (d - 1)`, then `X` is a `μ`-local spectral
expander (Definition 2.1, p.13), where `μ = lam / (1 - (d - 2) lam)`.

Das, Hopkins, Ray, Tung, *Concentration on HDX: Simplified and Optimized*, STOC 2027 submission (manuscript
sha256 ea5bee5f…).

**Formalization Note.** `X^{≤ d-2}` of Definition 2.1 is the set of faces with at most `d - 2` vertices, including
`∅`, and connectivity is asked of their links (see `IsTopLinkExpander`). `lam` is any real below `1 / (d - 1)`, as printed
in the theorem; a negative `lam` is allowed and the denominator is positive throughout. -/
theorem theorem_2_3 {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} (hd : 2 ≤ d)
    {X : Finset (Finset V)} {π : Finset V → ℝ} (hX : SteurerHDX.IsPure X d) (hπ : IsTopDensity X d π)
    (hconn : LinksConnected X d) {lam : ℝ} (hlam : lam < 1 / ((d : ℝ) - 1))
    (hlink : ∀ s ∈ X, s.card + 2 = d → SecondEigLE (linkVerts X s) (linkWeight X d π s) lam) :
    ∀ s ∈ X, s.card + 2 ≤ d →
      SecondEigLE (linkVerts X s) (linkWeight X d π s) (lam / (1 - ((d : ℝ) - 2) * lam)) := by sorry

end HDXConc
