-- Prove2me | Theorems.Thm_HDXConc_eq_13
-- name    : HDXConc.eq_13
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:00:37.785205+00:00
-- url     : https://prove2.me/theorems/ab1e8195-fc1f-432a-9937-af371e9a0d2f
-- title:
--   Eq. (13), p.15 — $\psi(t)=\tfrac12t^2\psi''(\theta t)\le dt^2/(4\eta)$
-- statement:
--   Let $X$ be a $\frac{1-\eta}{d-1}$-top-link expander for some $\eta\in(0,1]$, with $d\ge2$, let $f:X(1)\to[0,1]$, and let $\psi(t)=\log\mathbb E_{\pi_d}\exp(t(F-\mathbb E_{\pi_d}F))$. For every $t$ with $|t|\le\eta/2$ there is $\theta\in[0,1]$ with
--
--   $$\psi(t)=\frac12t^2\psi''(\theta t),$$
--
--   and moreover
--
--   $$\psi(t)\le\frac{dt^2}{4\eta}.$$
--
--   This is a sub-Gaussian bound on the log-moment generating function on the interval $|t|\le\eta/2$.
--
--   Differences from the source:
--   - encoding: the single chain ψ(t) = (1/2)t²ψ″(θt) ≤ dt²/(4η) → two clauses: ∃ θ ∈ [0, 1] with the equality, and ψ(t) ≤ dt²/(4η); reason: given the equality, the second inequality of the chain is the same in both forms
--   - encoding: ψ″ → iteratedDeriv 2 ψ; reason: ψ is smooth, so this is the second derivative
--   - reading: "the underlying graph of every link is connected" → connectivity for every s ∈ X with s.card + 2 ≤ d, including ∅; reason: read over all faces it would require the edgeless links of (d−1)-faces to be connected, excluding the complete complex and the paper's own example on p.18; footnote 2 and the only use (Theorem 2.3) concern these links, and this reading is the weaker hypothesis, so the theorem is the stronger one
--   - encoding: λ(X_s) ≤ λ, the second eigenvalue of the walk with weights π^s_2 → SecondEigLE (linkVerts X s) (linkWeight X d π s) λ, the Rayleigh quotient bound on the degree-orthogonal complement of the constants, with weights equal to π^s_2 up to a constant per link; reason: Courant–Fischer gives the equivalence, and a constant factor does not change the walk
--   - encoding: a d-dimensional (pure) complex, with co-dimension 2 links and d − 1 in denominators → 2 ≤ d and SteurerHDX.IsPure X d, with X a Finset (Finset V) over a finite type V; reason: this is the domain the statement is written for; dimension is the number of vertices, as in the paper, and the top density rules out the empty collection
--   - encoding: π_d : X(d) → (0, 1] a probability density → π : Finset V → ℝ, positive on X(d) with total mass 1 there, never read elsewhere; reason: the bound by 1 follows, and values off X(d) do not occur
--   - encoding: f : X(1) → [0, 1] → f : V → ℝ with 0 ≤ f v ≤ 1 whenever {v} ∈ X; reason: values off X(1) are never read, and no condition is imposed on them
-- source:
--   Das, Hopkins, Ray, Tung, Concentration on HDX: Simplified and Optimized, STOC 2027 submission (manuscript sha256 ea5bee5f…), eq. (13), p.15

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_HDXConc_IsTopDensity
import Definitions.Def_HDXConc_IsTopLinkExpander
import Definitions.Def_HDXConc_logMGF

namespace HDXConc

/-- Eq. (13), p.15: for `|t| ≤ η/2`, for some `θ ∈ [0, 1]`, `ψ(t) = (1/2) t² ψ''(θ t) ≤ d t² / (4 η)`.

Das, Hopkins, Ray, Tung, *Concentration on HDX: Simplified and Optimized*, STOC 2027 submission (manuscript
sha256 ea5bee5f…).

**Formalization Note.** `ψ''` is `iteratedDeriv 2 ψ`. `ψ` is the logarithm of a positive finite sum of exponentials, so
it is smooth and neither the logarithm nor the derivative takes a junk value. Both printed clauses are stated. -/
theorem eq_13 {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} (hd : 2 ≤ d) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1) {X : Finset (Finset V)} {π : Finset V → ℝ} (hX : SteurerHDX.IsPure X d)
    (hπ : IsTopDensity X d π) (hexp : IsTopLinkExpander X d π ((1 - η) / ((d : ℝ) - 1)))
    (f : V → ℝ) (hf : ∀ v, ({v} : Finset V) ∈ X → 0 ≤ f v ∧ f v ≤ 1) {t : ℝ} (ht : |t| ≤ η / 2) :
    (∃ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 ∧
      logMGF X d π f t = (1 / 2) * t ^ 2 * iteratedDeriv 2 (logMGF X d π f) (θ * t)) ∧
    logMGF X d π f t ≤ (d : ℝ) * t ^ 2 / (4 * η) := by sorry

end HDXConc
