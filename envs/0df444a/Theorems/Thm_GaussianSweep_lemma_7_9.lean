-- Prove2me | Theorems.Thm_GaussianSweep_lemma_7_9
-- name    : GaussianSweep.lemma_7_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:07.546795+00:00
-- url     : https://prove2.me/theorems/fb7d3387-bf5f-421c-bf07-4cf895ce74c6
-- title:
--   Lemma 7.9 — concentration of local counts: a realization with distinct labels and all counts within $\lambda$
-- statement:
--   Let $G$ be a graph with $N$ vertices and $\Delta(G) \le \Delta$, where $\Delta \ge 2$; let $(Y_v)$ be labels of $G$ as in Definition 5.2 with underlying independent standard normal variables $(Z_w)_{w \in V(G)}$; let $\varrho \ge 0$ be an integer; and let $W_1, \dots, W_\mu$ be sums over $v \in V(G)$ of $[0,1]$-valued measurable functions of $(Z_w)_{w \in B_\varrho(v)}$. If $\lambda > 0$ and
--   $$
--   \mu N \Delta^{2\varrho} < 2\lambda^2,
--   $$
--   then some realization of $(Z_w)$ has pairwise distinct labels and $|W_i - \mathbb E W_i| < \lambda$ for all $i$.
--
--   This is the step that turns bounds on expected frontier sizes at finitely many thresholds into one labeling to which the layout lemmas apply.
--
--   **Formalization Note** A realization is a point $z : V \to \mathbb R$; expectations are integrals under the product of standard normals. The labels are those of Definition 5.2 for arbitrary arc lengths that are positive on arcs and an arbitrary radius $\hat R > 0$. The count $W_i$ is $\sum_v g_{i,v}(z|_{B_\varrho(v)})$ with $g_{i,v}$ measurable and $[0,1]$-valued.
--
--   Differences from the source:
--   - encoding: independent N(0, 1) variables (Z_w)_{w ∈ V(G)} → the coordinates of a point z : V → ℝ under the product measure Measure.pi (fun _ => gaussianReal 0 1); reason: canonical probability space of the family; same random vector
--   - encoding: some realization of (Z_w) → ∃ z : V → ℝ; reason: a realization is a value of the vector (Z_w)
--   - generalization: labels as in Definition 5.2 (regime (a) or (b)) → Gaussian labels for any arc lengths positive on arcs and any R̂ > 0; reason: regimes (a) and (b) have positive lengths and R̂ > 0
--   - generalization: Δ(G) ≤ ∆ with ∆ ≥ 2 → a real number ∆ ≥ 2; reason: contains every integer ∆ ≥ 2
--   - encoding: a finite simple graph G → a SimpleGraph on a finite vertex type V (Fintype), n = card V; reason: every finite graph is isomorphic to one on a finite type; pathwidth and degrees are invariant
--   - encoding: W_i a sum over v of [0, 1]-valued measurable functions of (Z_w)_{w ∈ B_ϱ(v)} → ∑_v g i v (z restricted to B_ϱ(v)) with g i v measurable and g i v x ∈ [0, 1] for every x; reason: any such function factors through the restriction, and the factor may be clamped to [0, 1]
--   - encoding: E W_i → the integral of W_i under the product measure; reason: W_i is bounded and measurable, hence integrable
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 7.9, p.42 (PDF p.44)

import Mathlib
import Definitions.Def_GaussianSweep_ball
import Definitions.Def_GaussianSweep_gaussLabel
open MeasureTheory ProbabilityTheory

namespace GaussianSweep

/-- Lemma 7.9 (concentration of local counts) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 7.9, p.42 (PDF p.44)). Let `G` be a
graph with `N` vertices and `Δ(G) ≤ ∆`, where `∆ ≥ 2`, `(Y_v)` labels of `G` as in Definition 5.2
with underlying variables `(Z_w)`, `ϱ ≥ 0` an integer, and `W₁, …, W_µ` sums over `v ∈ V(G)` of
`[0, 1]`-valued measurable functions of `(Z_w)_{w ∈ B_ϱ(v)}`. If `λ > 0` and `µN∆^{2ϱ} < 2λ²`,
then some realization of `(Z_w)` has pairwise distinct labels and `|Wᵢ − EWᵢ| < λ` for all `i`.

**Formalization Note** The labels are those of Definition 5.2 for any arc lengths that are
positive on arcs and any `R̂ > 0` (this covers both regimes (a) and (b)). A realization is a point
`z : V → ℝ`; `E` is the integral under `Measure.pi fun _ => gaussianReal 0 1`. The count `Wᵢ` is
`∑_v g i v (z restricted to B_ϱ(v))` with `g i v` measurable and valued in `[0, 1]`. -/
theorem lemma_7_9 {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ)
    (hΔ2 : 2 ≤ Δ) (hΔ : (G.maxDegree : ℝ) ≤ Δ) (len : V → V → ℝ)
    (hlen : ∀ x y, G.Adj x y → 0 < len x y) (Rhat : ℝ) (hRhat : 0 < Rhat) (ϱ m : ℕ)
    (g : Fin m → (v : V) → (ball G v ϱ → ℝ) → ℝ) (hgm : ∀ i v, Measurable (g i v))
    (hg01 : ∀ i v x, g i v x ∈ Set.Icc 0 1) (lam : ℝ) (hlam : 0 < lam)
    (hcount : (m : ℝ) * Fintype.card V * Δ ^ (2 * ϱ) < 2 * lam ^ 2) :
    ∃ z : V → ℝ, Function.Injective (fun v => gaussLabel G len Rhat v z) ∧
      ∀ i, |∑ v, g i v (fun w => z w) -
          ∫ z', ∑ v, g i v (fun w => z' w) ∂(Measure.pi fun _ : V => gaussianReal 0 1)| < lam := by sorry

end GaussianSweep
