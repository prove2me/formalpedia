-- Prove2me | Theorems.Thm_HDXConc_claim_3_2
-- name    : HDXConc.claim_3_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:00:19.835959+00:00
-- url     : https://prove2.me/theorems/f2c8377b-c0b7-4a66-ac50-4760d10f9d0f
-- title:
--   Claim 3.2, p.15 — $1+(d-1)\lambda_2(A_t)\le 2/\eta$ for $|t|\le\eta/2$
-- statement:
--   Let $X$ be a $\frac{1-\eta}{d-1}$-top-link expander for some $\eta\in(0,1]$, with $d\ge2$, and let $f:X(1)\to[0,1]$. For every $t\in\mathbb R$ with $|t|\le\eta/2$,
--
--   $$1+(d-1)\lambda_2(A_t)\le\frac2\eta,$$
--
--   where $A_t$ is the random walk on the underlying graph of $X$ with the edge weights $\pi_{2,t}$ induced by the tilted density $\pi_{d,t}$.
--
--   This bound on the tilted one-skeleton is what makes the variance of the sum uniformly bounded along the tilt.
--
--   Differences from the source:
--   - encoding: 1 + (d − 1)λ₂(A_t) ≤ 2/η, with weights π_{2,t} → SecondEigLE (linkVerts X ∅) (linkWeight X d π_{d,t} ∅) ((2/η − 1)/(d − 1)); reason: d ≥ 2 makes the two inequalities equivalent; the weights are π_{2,t} times the constant (d choose 2), so the walk is the same
--   - reading: "the underlying graph of every link is connected" → connectivity for every s ∈ X with s.card + 2 ≤ d, including ∅; reason: read over all faces it would require the edgeless links of (d−1)-faces to be connected, excluding the complete complex and the paper's own example on p.18; footnote 2 and the only use (Theorem 2.3) concern these links, and this reading is the weaker hypothesis, so the theorem is the stronger one
--   - encoding: λ(X_s) ≤ λ, the second eigenvalue of the walk with weights π^s_2 → SecondEigLE (linkVerts X s) (linkWeight X d π s) λ, the Rayleigh quotient bound on the degree-orthogonal complement of the constants, with weights equal to π^s_2 up to a constant per link; reason: Courant–Fischer gives the equivalence, and a constant factor does not change the walk
--   - encoding: a d-dimensional (pure) complex, with co-dimension 2 links and d − 1 in denominators → 2 ≤ d and SteurerHDX.IsPure X d, with X a Finset (Finset V) over a finite type V; reason: this is the domain the statement is written for; dimension is the number of vertices, as in the paper, and the top density rules out the empty collection
--   - encoding: π_d : X(d) → (0, 1] a probability density → π : Finset V → ℝ, positive on X(d) with total mass 1 there, never read elsewhere; reason: the bound by 1 follows, and values off X(d) do not occur
--   - encoding: f : X(1) → [0, 1] → f : V → ℝ with 0 ≤ f v ≤ 1 whenever {v} ∈ X; reason: values off X(1) are never read, and no condition is imposed on them
-- source:
--   Das, Hopkins, Ray, Tung, Concentration on HDX: Simplified and Optimized, STOC 2027 submission (manuscript sha256 ea5bee5f…), Claim 3.2, p.15 (proof p.16)

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_HDXConc_IsTopDensity
import Definitions.Def_HDXConc_IsTopLinkExpander
import Definitions.Def_HDXConc_tilt

namespace HDXConc

/-- Claim 3.2, p.15 (proof p.16): for any `t ∈ ℝ` with `|t| ≤ η/2`, `1 + (d - 1) λ₂(A_t) ≤ 2/η`.

Das, Hopkins, Ray, Tung, *Concentration on HDX: Simplified and Optimized*, STOC 2027 submission (manuscript
sha256 ea5bee5f…).

**Formalization Note.** `A_t` is the walk on the underlying graph of `X` with weights `π_{2,t}`. The weights
`linkWeight X d π_{d,t} ∅` are `π_{2,t}` times the constant `d choose 2`, so they give the same walk. Since `d ≥ 2`,
`1 + (d - 1) λ₂(A_t) ≤ 2/η` is the same as `λ₂(A_t) ≤ (2/η - 1)/(d - 1)`, which is what `SecondEigLE` states. -/
theorem claim_3_2 {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} (hd : 2 ≤ d) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1) {X : Finset (Finset V)} {π : Finset V → ℝ} (hX : SteurerHDX.IsPure X d)
    (hπ : IsTopDensity X d π) (hexp : IsTopLinkExpander X d π ((1 - η) / ((d : ℝ) - 1)))
    (f : V → ℝ) (hf : ∀ v, ({v} : Finset V) ∈ X → 0 ≤ f v ∧ f v ≤ 1) {t : ℝ} (ht : |t| ≤ η / 2) :
    SecondEigLE (linkVerts X ∅) (linkWeight X d (tilt X d π f t) ∅) ((2 / η - 1) / ((d : ℝ) - 1)) := by sorry

end HDXConc
