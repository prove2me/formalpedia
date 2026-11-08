-- Prove2me | Theorems.Thm_GaussianSweep_lemma_5_6
-- name    : GaussianSweep.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:09.739443+00:00
-- url     : https://prove2.me/theorems/8d48d1f0-249b-4ed5-94a9-e2a14491e217
-- title:
--   Lemma 5.6 — distinctness and locality of Gaussian labels
-- statement:
--   Let $(Y_v)$ be the Gaussian labels of a finite graph $G$ in either regime of Definition 5.2:
--
--   - padded labels of degree $p$ at radius $R$, for integers $p \ge 3$, $R \ge 1$ and $\Delta(G) \le p$, with $\rho = R$;
--   - mixed labels at radius $R$, for real $R > 0$ and minimum degree $\delta(G) \ge 3$, with $\rho = \lfloor 2R/\ln 2\rfloor$.
--
--   Then:
--
--   1. $(Y_v)_{v \in V(G)}$ is a centered Gaussian vector, $\mathrm{Var}\,Y_v = 1$ and $\sigma_v \ge 1$ for every $v$;
--   2. the labels are pairwise distinct with probability $1$;
--   3. $B(v) \subseteq B_\rho(v)$, so $Y_v$ is a function of $(Z_w)_{w \in B_\rho(v)}$;
--   4. for every $t \in \mathbb R$ the events $\{v \in \partial^+ S_t\}$ and $\{v \in \partial^- S_t\}$ for the labeling $Y$ are determined by $(Z_w)_{w \in B_{\rho+1}(v)}$.
--
--   Distinctness is what the layout lemmas need, and locality is what makes frontier counts concentrate.
--
--   **Formalization Note** "Centered Gaussian vector" is stated as: every finite family of labels has a Gaussian joint law (`IsGaussianProcess`) and every label has mean $0$. "Is a function of" and "is determined by" the variables on a set $B$ are stated as: two points $z, z'$ that agree on $B$ give the same label, respectively the same frontier membership.
--
--   Differences from the source:
--   - encoding: independent N(0, 1) variables (Z_w)_{w ∈ V(G)} → the coordinates of a point z : V → ℝ under the product measure Measure.pi (fun _ => gaussianReal 0 1); reason: canonical probability space of the family; same random vector
--   - encoding: (Y_v) is a centered Gaussian vector → IsGaussianProcess of the label family under the product measure, and mean 0 of every label; reason: a family is a Gaussian vector iff all its finite-dimensional laws are Gaussian
--   - encoding: Y_v is a function of (Z_w)_{w ∈ B}; the events are determined by (Z_w)_{w ∈ B} → two points z, z' agreeing on B give the same label, resp. the same frontier membership; reason: this is the meaning of measurable dependence on the coordinates in B
--   - encoding: δ(G) ≥ 3 → ∀ v, 3 ≤ G.degree v; reason: same graphs (and avoids Mathlib's minDegree = 0 on the empty graph)
--   - encoding: a finite simple graph G → a SimpleGraph on a finite vertex type V (Fintype), n = card V; reason: every finite graph is isomorphic to one on a finite type; pathwidth and degrees are invariant
--   - encoding: labels in either regime → a conjunction of one clause for the padded regime (all p, R) and one for the mixed regime (all R); reason: the same two families of labels, each with its hypotheses from Definition 5.2
--   - encoding: ρ = ⌊2R/ln 2⌋ → the natural-number floor ⌊2 * R / Real.log 2⌋₊; reason: R > 0, so the argument is positive and the two floors agree
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 5.6, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_GaussianSweep_ball
import Definitions.Def_GaussianSweep_labelBall
import Definitions.Def_GaussianSweep_labelSigma
import Definitions.Def_GaussianSweep_paddedLabel
import Definitions.Def_GaussianSweep_mixedLabel
import Definitions.Def_GaussianSweep_outerFrontier
import Definitions.Def_GaussianSweep_innerFrontier
open MeasureTheory ProbabilityTheory

namespace GaussianSweep

/-- Lemma 5.6 (distinctness and locality) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 5.6, p.30 (PDF p.32)). Let `(Y_v)` be
labels as in Definition 5.2, in either regime, and put `ρ = R` for padded labels and
`ρ = ⌊2R/ln 2⌋` for mixed labels. Then (i) `(Y_v)` is a centered Gaussian vector, `Var Y_v = 1`
and `σ_v ≥ 1`; (ii) the labels are pairwise distinct with probability 1; (iii) `B(v) ⊆ B_ρ(v)`,
so `Y_v` is a function of `(Z_w)_{w ∈ B_ρ(v)}`; (iv) for every `t`, the events `v ∈ ∂⁺S_t` and
`v ∈ ∂⁻S_t` for the labeling `Y` are determined by `(Z_w)_{w ∈ B_{ρ+1}(v)}`.

The first conjunct is the padded regime (integers `p ≥ 3`, `R ≥ 1`, `Δ(G) ≤ p`), the second the
mixed regime (real `R > 0`, `δ(G) ≥ 3`).

**Formalization Note** `(Z_w)` are the coordinates of `z : V → ℝ` under
`Measure.pi fun _ => gaussianReal 0 1`. "Centered Gaussian vector" is `IsGaussianProcess` (every
finite-dimensional marginal is Gaussian) together with mean zero for every coordinate. "Is a
function of" / "is determined by" `(Z_w)_{w ∈ B}` is: two points agreeing on `B` give the same
value / the same membership. `δ(G) ≥ 3` is `∀ v, 3 ≤ G.degree v`. -/
theorem lemma_5_6 {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∀ p R : ℕ, 3 ≤ p → 1 ≤ R → G.maxDegree ≤ p →
      IsGaussianProcess (paddedLabel G p R) (Measure.pi fun _ : V => gaussianReal 0 1) ∧
      (∀ v, ∫ z, paddedLabel G p R v z ∂(Measure.pi fun _ : V => gaussianReal 0 1) = 0 ∧
        Var[paddedLabel G p R v; Measure.pi fun _ : V => gaussianReal 0 1] = 1 ∧
        1 ≤ labelSigma G (fun _ _ => Real.log ((p : ℝ) - 1) / 2) ((R : ℝ) / 2 * Real.log ((p : ℝ) - 1)) v) ∧
      (Measure.pi fun _ : V => gaussianReal 0 1)
        {z | ¬ Function.Injective fun v => paddedLabel G p R v z} = 0 ∧
      (∀ v, labelBall G (fun _ _ => Real.log ((p : ℝ) - 1) / 2) ((R : ℝ) / 2 * Real.log ((p : ℝ) - 1)) v ⊆ ball G v (R) ∧
        ∀ z z' : V → ℝ, (∀ w ∈ ball G v (R), z w = z' w) →
          paddedLabel G p R v z = paddedLabel G p R v z') ∧
      (∀ v (t : ℝ) (z z' : V → ℝ), (∀ w ∈ ball G v (R + 1), z w = z' w) →
        (v ∈ outerFrontier G (fun x => paddedLabel G p R x z) t ↔
          v ∈ outerFrontier G (fun x => paddedLabel G p R x z') t) ∧
        (v ∈ innerFrontier G (fun x => paddedLabel G p R x z) t ↔
          v ∈ innerFrontier G (fun x => paddedLabel G p R x z') t))) ∧
    (∀ R : ℝ, 0 < R → (∀ v, 3 ≤ G.degree v) →
      IsGaussianProcess (mixedLabel G R) (Measure.pi fun _ : V => gaussianReal 0 1) ∧
      (∀ v, ∫ z, mixedLabel G R v z ∂(Measure.pi fun _ : V => gaussianReal 0 1) = 0 ∧
        Var[mixedLabel G R v; Measure.pi fun _ : V => gaussianReal 0 1] = 1 ∧
        1 ≤ labelSigma G (fun x _ => Real.log ((G.degree x : ℝ) - 1) / 2) R v) ∧
      (Measure.pi fun _ : V => gaussianReal 0 1)
        {z | ¬ Function.Injective fun v => mixedLabel G R v z} = 0 ∧
      (∀ v, labelBall G (fun x _ => Real.log ((G.degree x : ℝ) - 1) / 2) R v ⊆ ball G v (⌊2 * R / Real.log 2⌋₊) ∧
        ∀ z z' : V → ℝ, (∀ w ∈ ball G v (⌊2 * R / Real.log 2⌋₊), z w = z' w) →
          mixedLabel G R v z = mixedLabel G R v z') ∧
      (∀ v (t : ℝ) (z z' : V → ℝ), (∀ w ∈ ball G v (⌊2 * R / Real.log 2⌋₊ + 1), z w = z' w) →
        (v ∈ outerFrontier G (fun x => mixedLabel G R x z) t ↔
          v ∈ outerFrontier G (fun x => mixedLabel G R x z') t) ∧
        (v ∈ innerFrontier G (fun x => mixedLabel G R x z) t ↔
          v ∈ innerFrontier G (fun x => mixedLabel G R x z') t))) := by sorry

end GaussianSweep
