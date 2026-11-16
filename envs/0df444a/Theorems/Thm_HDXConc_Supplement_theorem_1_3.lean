-- Prove2me | Theorems.Thm_HDXConc_Supplement_theorem_1_3
-- name    : HDXConc.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:35:16.526565+00:00
-- url     : https://prove2.me/theorems/e3a03876-4810-4f3e-8596-1b68401ffe63
-- title:
--   Theorem 1.3, p.4 — hitting-set bound $\mu(\mu+(d-1)\lambda)^{d-1}$ on one-sided $\lambda$-local-spectral expanders
-- statement:
--   Let $X$ be a pure $d$-dimensional simplicial complex on a finite vertex set $V$, $d\ge1$, where the dimension of a face is its number of vertices, so $X(1)$ is the vertex level and $X(d)$ the top level. Let $\pi_d$ be a positive probability density on $X(d)$ and $\pi_1(v)=\frac1d\sum_{\sigma\in X(d),\,\sigma\ni v}\pi_d(\sigma)$ the induced vertex measure. Let $\lambda\ge0$, and suppose $X$ is a **one-sided $\lambda$-local-spectral expander** (Definition 2.1): for every face $s$ with at most $d-2$ vertices, the empty face included, the second largest eigenvalue $\lambda(X_s)$ of the random walk on the underlying weighted graph of the link $X_s$ is at most $\lambda$. Then:
--
--   1. for every $A\subseteq V$, writing $\mu=\pi_1(A)=\sum_{v\in A}\pi_1(v)$,
--   $$\Pr_{\sigma\sim\pi_d}[\sigma\subseteq A]\le\mu\,\big(\mu+(d-1)\lambda\big)^{d-1};\qquad(3)$$
--   2. more generally, for every $f:V\to[0,1]$, writing $\mu=\mathbb E_{\pi_1}f$,
--   $$\mathop{\mathbb E}_{\sigma\sim\pi_d}\Big[\prod_{v\in\sigma}f(v)\Big]\le\mu\,\big(\mu+(d-1)\lambda\big)^{d-1}.\qquad(4)$$
--
--   For $d$ independent samples from $\pi_1$ the probability of landing in $A$ is $\mu^d$; the theorem shows that a random top face of a local spectral expander behaves like this up to replacing $\mu$ by $\mu+(d-1)\lambda$ in all but one factor, the analogue of the classical hitting-set bound $\mu(\mu+\lambda)^{d-1}$ for random walks on expander graphs.
--
--   **Formalization Note** $X$ is a finite family of finite subsets of a finite type $V$, and $\pi_d$ is a real function on finite sets that is positive with total mass one on $X(d)$ and is never read elsewhere. The spectral condition is written in Rayleigh form: on the degree-orthogonal complement of the constants, the quadratic form of the link weights is at most $\lambda$ times the degree-weighted squared norm; the link weights are the paper's $\pi^s_2$ up to a constant factor per link, which does not change the walk. Probabilities and expectations under $\pi_d$ are finite sums over $X(d)$. The two inequalities are stated as one conjunction.
--
--   Differences from the source:
--   - generalization: λ ≥ 0, with Definition 2.1 written for λ ∈ (0, 1) → every real lam ≥ 0; reason: Theorem 1.3 itself assumes only λ ≥ 0; the printed range λ ∈ (0, 1) is an instance
--   - encoding: λ(X_s) ≤ λ, the second eigenvalue of the walk with weights π^s_2 → SecondEigLE (linkVerts X s) (linkWeight X d π s) lam, the Rayleigh quotient bound on the degree-orthogonal complement of the constants, with weights equal to π^s_2 up to a constant per link; reason: Courant–Fischer gives the equivalence, and a constant factor does not change the walk
--   - encoding: X a one-sided λ-local-spectral expander (Definition 2.1: every s ∈ X^{≤d−2}) → ∀ s ∈ X with s.card + 2 ≤ d, SecondEigLE at lam; reason: this is the definition spelled out; X^{≤d−2} includes ∅, whose link is X itself
--   - encoding: a d-dimensional (pure) complex → 1 ≤ d and SteurerHDX.IsPure X d, with X a Finset (Finset V) over a finite type V; reason: at d = 0 the exponent d − 1 and the measure π₁ are undefined; dimension is the number of vertices, as in the paper
--   - encoding: π_d : X(d) → (0, 1] a probability density → π : Finset V → ℝ, positive on X(d) with total mass 1 there, never read elsewhere; reason: the bound by 1 follows, and values off X(d) do not occur
--   - encoding: f : V → [0, 1] → f : V → ℝ with 0 ≤ f v ≤ 1 for every v with {v} ∈ X; reason: values of f off X(1) are never read by either side of (4)
--   - encoding: Pr_{σ∼π_d}[σ ⊆ A], E_{σ∼π_d}[·], µ = Σ_{v∈A} π₁(v), E_{π₁} f → finite sums of π over X(d), Σ_{v∈A} faceMeasure X d π 1 {v}, vertexMean X d π f; reason: these are the definitions; π₁ vanishes off X(1), so the sum over A equals the sum over A ∩ X(1)
-- source:
--   Das, Hopkins, Ray, Tung, Concentration on HDX: Simplified and Optimized, STOC 2027 submission (manuscript sha256 ea5bee5f…), Theorem 1.3, p.4 (restated p.19), eqs. (3), (4); Definition 2.1, p.13

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_HDXConc_IsTopDensity
import Definitions.Def_HDXConc_linkWeight
import Definitions.Def_HDXConc_SecondEigLE
import Definitions.Def_HDXConc_walkOp

namespace HDXConc.Supplement

open HDXConc

/-- Theorem 1.3 (Hitting-set bound), p.4 (restated p.19): let `X` be a `d`-dimensional, one-sided `lam`-local-spectral
expander with `lam ≥ 0`. For every `A ⊆ V`, writing `µ = π₁(A) = ∑_{v ∈ A} π₁(v)`,
`Pr_{σ ∼ π_d}[σ ⊆ A] ≤ µ (µ + (d - 1) lam)^(d - 1)` (eq. (3)); more generally, for every `f : V → [0, 1]` and
`µ = E_{π₁} f`, `E_{σ ∼ π_d}[∏_{v ∈ σ} f(v)] ≤ µ (µ + (d - 1) lam)^(d - 1)` (eq. (4)).

Das, Hopkins, Ray, Tung, *Concentration on HDX: Simplified and Optimized*, STOC 2027 submission (manuscript
sha256 ea5bee5f…); one-sided local spectral expansion is Definition 2.1, p.13.

**Formalization Note.** Dimension is the number of vertices (`X(1)` = vertices, `X(d)` = top faces), and `X` is a pure
`d`-dimensional complex with `d ≥ 1`; `π` is a positive probability density on `X(d)`, never read elsewhere, and
`π₁ = faceMeasure X d π 1`. The one-sided `lam`-local-spectral expansion of Definition 2.1 is spelled out: for every face
`s` with at most `d - 2` vertices, the empty face included (so the underlying graph of `X` itself), the second eigenvalue
of the walk on the link of `s` is at most `lam`, in the Rayleigh form `SecondEigLE` with the link weights `linkWeight`
(the paper's `π^s_2` up to a constant per link). Only `lam ≥ 0` is assumed, as in the theorem; Definition 2.1's
range `lam ∈ (0, 1)` is not imposed. Probabilities and expectations under `π_d` are finite sums over `X(d)`; `µ` in (3) is
the sum of `π₁` over `A` (it vanishes at non-vertices), and `µ` in (4) is `vertexMean`, the `π₁`-mean of `f`. `f` is
constrained to `[0, 1]` only on `X(1)`, the only points where it is read. The exponent `d - 1` is natural-number
subtraction, exact for `d ≥ 1`. -/
theorem theorem_1_3 {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} (hd : 1 ≤ d)
    {X : Finset (Finset V)} {π : Finset V → ℝ} (hX : SteurerHDX.IsPure X d) (hπ : IsTopDensity X d π)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hLSE : ∀ s ∈ X, s.card + 2 ≤ d → SecondEigLE (linkVerts X s) (linkWeight X d π s) lam) :
    (∀ A : Finset V,
      ∑ σ ∈ (SteurerHDX.faces X d).filter (fun σ => σ ⊆ A), π σ ≤
        (∑ v ∈ A, faceMeasure X d π 1 {v}) *
          ((∑ v ∈ A, faceMeasure X d π 1 {v}) + ((d : ℝ) - 1) * lam) ^ (d - 1)) ∧
    (∀ f : V → ℝ, (∀ v, ({v} : Finset V) ∈ X → 0 ≤ f v ∧ f v ≤ 1) →
      ∑ σ ∈ SteurerHDX.faces X d, π σ * ∏ v ∈ σ, f v ≤
        vertexMean X d π f * (vertexMean X d π f + ((d : ℝ) - 1) * lam) ^ (d - 1)) := by sorry

end HDXConc.Supplement
