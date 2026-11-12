-- Prove2me | Theorems.Thm_HDXConc_upper_tail
-- name    : HDXConc.upper_tail
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:00:17.874085+00:00
-- url     : https://prove2.me/theorems/3b69e113-a310-47d0-864f-9c2351fa7afd
-- title:
--   Proof of Theorem 1.1, p.15 — upper tail for $\alpha\in(0,1]$
-- statement:
--   Let $X$ be a $\frac{1-\eta}{d-1}$-top-link expander for some $\eta\in(0,1]$, with $d\ge2$, let $f:X(1)\to[0,1]$ and $F(\sigma)=\sum_{v\in\sigma}f(v)$. For every $\alpha\in(0,1]$,
--
--   $$\Pr_{\sigma\sim\pi_d}\big[F(\sigma)-\mathbb E_{\pi_d}[F]\ge\alpha d\big]\le\exp\Big(-\frac\eta4\alpha^2d\Big).$$
--
--   This is the one-sided form of the main theorem, with the non-strict inequality as printed.
--
--   Differences from the source:
--   - reading: Pr_{σ∼X(d)} and E_{X(d)}[F] → the finite sum of π_d over the event, and the π_d-mean of F; reason: p.14 writes s ∼ π_d for the same statement, and the proof works with E_{π_d}F in the line before
--   - reading: "the underlying graph of every link is connected" → connectivity for every s ∈ X with s.card + 2 ≤ d, including ∅; reason: read over all faces it would require the edgeless links of (d−1)-faces to be connected, excluding the complete complex and the paper's own example on p.18; footnote 2 and the only use (Theorem 2.3) concern these links, and this reading is the weaker hypothesis, so the theorem is the stronger one
--   - encoding: λ(X_s) ≤ λ, the second eigenvalue of the walk with weights π^s_2 → SecondEigLE (linkVerts X s) (linkWeight X d π s) λ, the Rayleigh quotient bound on the degree-orthogonal complement of the constants, with weights equal to π^s_2 up to a constant per link; reason: Courant–Fischer gives the equivalence, and a constant factor does not change the walk
--   - encoding: a d-dimensional (pure) complex, with co-dimension 2 links and d − 1 in denominators → 2 ≤ d and SteurerHDX.IsPure X d, with X a Finset (Finset V) over a finite type V; reason: this is the domain the statement is written for; dimension is the number of vertices, as in the paper, and the top density rules out the empty collection
--   - encoding: π_d : X(d) → (0, 1] a probability density → π : Finset V → ℝ, positive on X(d) with total mass 1 there, never read elsewhere; reason: the bound by 1 follows, and values off X(d) do not occur
--   - encoding: f : X(1) → [0, 1] → f : V → ℝ with 0 ≤ f v ≤ 1 whenever {v} ∈ X; reason: values off X(1) are never read, and no condition is imposed on them
-- source:
--   Das, Hopkins, Ray, Tung, Concentration on HDX: Simplified and Optimized, STOC 2027 submission (manuscript sha256 ea5bee5f…), Proof of Theorem 1.1, p.15

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_HDXConc_IsTopDensity
import Definitions.Def_HDXConc_IsTopLinkExpander
import Definitions.Def_HDXConc_tilt
import Definitions.Def_HDXConc_topVar

namespace HDXConc

/-- Proof of Theorem 1.1, p.15, the upper tail: for any `α ∈ (0, 1]`,
`Pr_{σ ∼ X(d)}[F(σ) - E_{X(d)}[F] ≥ α d] ≤ exp(-(η/4) α² d)`.

Das, Hopkins, Ray, Tung, *Concentration on HDX: Simplified and Optimized*, STOC 2027 submission (manuscript
sha256 ea5bee5f…).

**Formalization Note.** `σ ∼ X(d)` means `σ ∼ π_d` (p.14), so the probability is the finite sum of `π_d` over the event. -/
theorem upper_tail {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} (hd : 2 ≤ d) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1) {X : Finset (Finset V)} {π : Finset V → ℝ} (hX : SteurerHDX.IsPure X d)
    (hπ : IsTopDensity X d π) (hexp : IsTopLinkExpander X d π ((1 - η) / ((d : ℝ) - 1)))
    (f : V → ℝ) (hf : ∀ v, ({v} : Finset V) ∈ X → 0 ≤ f v ∧ f v ≤ 1) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α ≤ 1) :
    ∑ σ ∈ (SteurerHDX.faces X d).filter (fun σ => α * (d : ℝ) ≤ topSum f σ - topMean X d π (topSum f)), π σ ≤
      Real.exp (-(η / 4) * α ^ 2 * (d : ℝ)) := by sorry

end HDXConc
