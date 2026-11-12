-- Prove2me | Theorems.Thm_HDXConc_theorem_1_1
-- name    : HDXConc.theorem_1_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:00:23.46471+00:00
-- url     : https://prove2.me/theorems/4ce109a3-aba4-4d41-ba32-9d7722bec5e7
-- title:
--   Theorem 1.1, p.3 — sub-Gaussian Chernoff bound $2\exp(-\eta\alpha^2d/4)$ for every $\frac{1-\eta}{d-1}$-top-link expander
-- statement:
--   Let $d\ge2$, $\eta\in(0,1]$, and let $X$ be a pure $d$-dimensional simplicial complex with a positive probability density $\pi_d$ on its top level $X(d)$, which is a $\frac{1-\eta}{d-1}$-top-link expander. Then for every $f:X(1)\to[0,1]$ and every $\alpha>0$,
--
--   $$\Pr_{s\sim\pi_d}\Big[\Big|\frac1d\sum_{v\in s}f(v)-\mathbb E[f]\Big|>\alpha\Big]\le2\exp\Big(-\frac\eta4\alpha^2d\Big),$$
--
--   where $\mathbb E[f]=\sum_{v\in X(1)}\pi_1(v)f(v)$ is the mean under the vertex marginal of $\pi_d$.
--
--   So the average of $f$ over a random top face concentrates like the average of $d$ independent bounded variables, with a rate that degrades only by the factor $\eta$, for every top-link expansion below the threshold $\frac{1}{d-1}$.
--
--   Differences from the source:
--   - reading: "the underlying graph of every link is connected" → connectivity for every s ∈ X with s.card + 2 ≤ d, including ∅; reason: read over all faces it would require the edgeless links of (d−1)-faces to be connected, excluding the complete complex and the paper's own example on p.18; footnote 2 and the only use (Theorem 2.3) concern these links, and this reading is the weaker hypothesis, so the theorem is the stronger one
--   - reading: E[f], unadorned on p.3 → the mean of f under the marginal π₁; reason: p.15 states E_{π_d}[F] = d E_{π₁}[f], and the concentration is around this value
--   - encoding: λ(X_s) ≤ λ, the second eigenvalue of the walk with weights π^s_2 → SecondEigLE (linkVerts X s) (linkWeight X d π s) λ, the Rayleigh quotient bound on the degree-orthogonal complement of the constants, with weights equal to π^s_2 up to a constant per link; reason: Courant–Fischer gives the equivalence, and a constant factor does not change the walk
--   - encoding: λ ∈ [0, 1) in Definition 2.4 → not part of the predicate IsTopLinkExpander; reason: the value (1 − η)/(d − 1) lies in [0, 1) for η ∈ (0, 1] and d ≥ 2
--   - encoding: Pr_{s∼π_d}[·] → the finite sum of π over the event inside X(d); reason: X(d) is finite and π is its density
--   - encoding: a d-dimensional (pure) complex, with co-dimension 2 links and d − 1 in denominators → 2 ≤ d and SteurerHDX.IsPure X d, with X a Finset (Finset V) over a finite type V; reason: this is the domain the statement is written for; dimension is the number of vertices, as in the paper, and the top density rules out the empty collection
--   - encoding: π_d : X(d) → (0, 1] a probability density → π : Finset V → ℝ, positive on X(d) with total mass 1 there, never read elsewhere; reason: the bound by 1 follows, and values off X(d) do not occur
--   - encoding: f : X(1) → [0, 1] → f : V → ℝ with 0 ≤ f v ≤ 1 whenever {v} ∈ X; reason: values off X(1) are never read, and no condition is imposed on them
-- source:
--   Das, Hopkins, Ray, Tung, Concentration on HDX: Simplified and Optimized, STOC 2027 submission (manuscript sha256 ea5bee5f…), Theorem 1.1, p.3 (restated p.14)

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_HDXConc_IsTopDensity
import Definitions.Def_HDXConc_IsTopLinkExpander
import Definitions.Def_HDXConc_walkOp

namespace HDXConc

/-- Theorem 1.1, p.3 (restated p.14): let `X` be a `(1 - η)/(d - 1)`-top-link expander for some `η ∈ (0, 1]`. Then for
every `f : X(1) → [0, 1]` and every `α > 0`,
`Pr_{s ∼ π_d}[|(1/d) ∑_{v ∈ s} f(v) - E[f]| > α] ≤ 2 exp(-(η/4) α² d)`.

Das, Hopkins, Ray, Tung, *Concentration on HDX: Simplified and Optimized*, STOC 2027 submission (manuscript
sha256 ea5bee5f…).

**Formalization Note.** Here `X` is a pure `d`-dimensional complex with `d ≥ 2` (co-dimension `2` and `d - 1` in the
denominator need it), dimension meaning number of vertices, and `π` is a positive probability density on `X(d)`. `f` is
constrained only on `X(1)`; its values on other points of `V` are never read. `E[f]` is the mean under the marginal `π₁`
(p.15: `E_{π_d}[F] = d E_{π₁}[f]`), and the probability is the finite sum of `π_d` over the event. -/
theorem theorem_1_1 {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} (hd : 2 ≤ d) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1) {X : Finset (Finset V)} {π : Finset V → ℝ} (hX : SteurerHDX.IsPure X d)
    (hπ : IsTopDensity X d π) (hexp : IsTopLinkExpander X d π ((1 - η) / ((d : ℝ) - 1)))
    (f : V → ℝ) (hf : ∀ v, ({v} : Finset V) ∈ X → 0 ≤ f v ∧ f v ≤ 1) {α : ℝ} (hα : 0 < α) :
    ∑ s ∈ (SteurerHDX.faces X d).filter
        (fun s => α < |(1 / (d : ℝ)) * ∑ v ∈ s, f v - vertexMean X d π f|), π s ≤
      2 * Real.exp (-(η / 4) * α ^ 2 * (d : ℝ)) := by sorry

end HDXConc
