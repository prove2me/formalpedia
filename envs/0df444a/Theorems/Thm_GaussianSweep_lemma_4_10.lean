-- Prove2me | Theorems.Thm_GaussianSweep_lemma_4_10
-- name    : GaussianSweep.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:14.920945+00:00
-- url     : https://prove2.me/theorems/71bdcb76-71b7-4393-8a52-cabded0fc88e
-- title:
--   Lemma 4.10 — local variance: $\mathrm{Var}\,W \le \frac{a^2}{4}\#\{(u,v): A_u\cap A_v\ne\emptyset\}$
-- statement:
--   Let $G$ be a graph with $n$ vertices, let $(Z_w)_{w \in V(G)}$ be independent real random variables, and for every vertex $v$ let $A_v \subseteq V(G)$ and let $I_v$ be a random variable with values in $[0, a]$ that is a measurable function of $(Z_w)_{w \in A_v}$. Put $W = \sum_v I_v$. Then
--   $$
--   \mathrm{Var}\, W \le \frac{a^2}{4}\cdot \#\{(u, v) \in V(G)^2 : A_u \cap A_v \ne \emptyset\}.
--   $$
--   If moreover $\Delta(G) \le \Delta$ for some $\Delta \ge 2$ and $A_v \subseteq B_\rho(v)$ for every $v$, then
--   $$
--   \mathrm{Var}\, W \le \frac{a^2}{4}\, n \max_v |B_{2\rho}(v)| \le \frac{a^2}{2}\, n \Delta^{2\rho}
--   \qquad\text{and}\qquad
--   \mathbb P\big(|W - \mathbb E W| \ge \lambda\big) \le \frac{a^2 n \Delta^{2\rho}}{2\lambda^2} \ \text{ for every } \lambda > 0 .
--   $$
--   Frontier sizes of a labeling by local labels are sums of this kind, so the lemma makes them concentrate.
--
--   **Formalization Note** The $Z_w$ live on a probability space, are measurable and mutually independent, with arbitrary laws. $I_v = g_v\big((Z_w)_{w \in A_v}\big)$ with $g_v$ measurable on $\mathbb R^{A_v}$ and valued in $[0, a]$. The maximum over $v$ is $0$ on an empty vertex set, and $\rho$ is a natural number.
--
--   Differences from the source:
--   - encoding: I_v a random variable with values in [0, a] that is a measurable function of (Z_w)_{w ∈ A_v} → I_v = g_v ∘ (restriction of Z to A_v) with g_v measurable and g_v(x) ∈ [0, a] for every x; reason: any such I_v is g_v ∘ restriction for a measurable g_v, which may be clamped to [0, a] without changing I_v
--   - encoding: independent random variables (Z_w) → measurable Z_w : Ω → ℝ with iIndepFun Z P on a probability space; reason: the standard meaning
--   - generalization: Δ(G) ≤ ∆ for some ∆ ≥ 2 → a real number ∆ ≥ 2 with Δ(G) ≤ ∆; reason: contains every integer ∆ ≥ 2
--   - encoding: a finite simple graph G → a SimpleGraph on a finite vertex type V (Fintype), n = card V; reason: every finite graph is isomorphic to one on a finite type; pathwidth and degrees are invariant
--   - encoding: the first bound, stated for a graph G with n vertices → stated for the finite vertex type V, with G quantified only in the second part; reason: G plays no role in the first bound
--   - encoding: max_v |B_{2ρ}(v)| → Finset.univ.sup over v, with value 0 on an empty vertex set; reason: the maximum for n ≥ 1; at n = 0 the bounds read 0 ≤ 0
--   - encoding: the ball radius ρ → ρ : ℕ; reason: radii of the balls B_k(v) of Section 4.1 are natural numbers
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 4.10, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_GaussianSweep_ball
open MeasureTheory ProbabilityTheory

namespace GaussianSweep

/-- Lemma 4.10 (local variance) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 4.10, p.27 (PDF p.29)). Let `G` be a graph with `n`
vertices, `(Z_w)_{w ∈ V(G)}` independent random variables, and for every vertex `v` let
`A_v ⊆ V(G)` and `I_v` a random variable with values in `[0, a]` that is a measurable function of
`(Z_w)_{w ∈ A_v}`. Put `W = ∑_v I_v`. Then `Var W ≤ (a²/4)·#{(u, v) ∈ V(G)² : A_u ∩ A_v ≠ ∅}`.
If moreover `Δ(G) ≤ ∆` for some `∆ ≥ 2` and `A_v ⊆ B_ρ(v)` for every `v`, then
`Var W ≤ (a²/4) n max_v |B_{2ρ}(v)| ≤ (a²/2) n ∆^{2ρ}` and
`P(|W − EW| ≥ λ) ≤ a² n ∆^{2ρ}/(2λ²)` for every `λ > 0`.

**Formalization Note** The `Z_w` are real random variables on a probability space `(Ω, P)`,
measurable and mutually independent (`iIndepFun`), of arbitrary laws. `I_v = g_v((Z_w)_{w ∈ A_v})`
with `g_v : (A_v → ℝ) → ℝ` measurable and valued in `[0, a]` (a random variable with values in
`[0, a]` that is a measurable function of `(Z_w)_{w ∈ A_v}` can always be written so, by clamping
`g_v`). The first bound needs no graph; the graph enters only the second part. `max_v` is
`Finset.sup` (`0` on an empty vertex set); `∆` is real and `ρ` a natural number. -/
theorem lemma_4_10 {V Ω : Type} [Fintype V] [DecidableEq V] [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : V → Ω → ℝ) (hZm : ∀ w, Measurable (Z w)) (hZ : iIndepFun Z P)
    (A : V → Finset V) (a : ℝ) (g : (v : V) → (A v → ℝ) → ℝ) (hgm : ∀ v, Measurable (g v))
    (hga : ∀ v x, g v x ∈ Set.Icc 0 a) :
    Var[fun ω => ∑ v, g v (fun w => Z w ω); P] ≤
        a ^ 2 / 4 * ((Finset.univ.filter fun uv : V × V => (A uv.1 ∩ A uv.2).Nonempty).card : ℝ) ∧
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ), 2 ≤ Δ → (G.maxDegree : ℝ) ≤ Δ →
      ∀ ρ : ℕ, (∀ v, A v ⊆ ball G v ρ) →
        Var[fun ω => ∑ v, g v (fun w => Z w ω); P] ≤
            a ^ 2 / 4 * Fintype.card V * (Finset.univ.sup fun v => (ball G v (2 * ρ)).card : ℕ) ∧
        a ^ 2 / 4 * Fintype.card V * (Finset.univ.sup fun v => (ball G v (2 * ρ)).card : ℕ) ≤
            a ^ 2 / 2 * Fintype.card V * Δ ^ (2 * ρ) ∧
        ∀ lam : ℝ, 0 < lam →
          P.real {ω | lam ≤ |∑ v, g v (fun w => Z w ω) - ∫ ω', ∑ v, g v (fun w => Z w ω') ∂P|} ≤
            a ^ 2 * Fintype.card V * Δ ^ (2 * ρ) / (2 * lam ^ 2) := by sorry

end GaussianSweep
