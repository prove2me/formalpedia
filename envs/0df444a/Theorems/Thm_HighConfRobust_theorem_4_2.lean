-- Prove2me | Theorems.Thm_HighConfRobust_theorem_4_2
-- name    : HighConfRobust.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:07:19.507777+00:00
-- url     : https://prove2.me/theorems/cdcc0179-e5e1-45f0-8672-2e6266ca389b
-- title:
--   Theorem 4.2 — under mild Lipschitzness, $g\circ A\circ f^{\otimes n}$ is $(\varepsilon, C^2(2K\alpha+\Delta), e^{-n\varepsilon}, \mathcal F)$-TV-robust
-- statement:
--   Consider a statistical task on a sample space $\mathcal X$ with output space $\mathcal Y$, parameter map $\theta$ and a loss $\mathrm{loss}:\mathcal Y\times\mathcal Y\to\mathbb R_{\ge0}$ that is symmetric and satisfies the approximate triangle inequality
--
--   $$
--   \mathrm{loss}(y_1,y_2)\le C\big(\mathrm{loss}(y_1,y_3)+\mathrm{loss}(y_3,y_2)\big)\qquad(C\ge1).
--   $$
--
--   Let $\mathcal F$ be a family of distributions, $f:\mathcal X\to\mathcal X$ a pre-processing map, $g:\mathcal Y\to\mathcal Y$ a post-processing map, and $a_*>0$, $L>0$, $K\ge0$, $\Delta$, $\alpha$ reals with
--
--   $$
--   a_*\le \alpha/L<1/2 .
--   $$
--
--   Suppose Assumption 4.1 holds:
--
--   1. with $\mathcal F_{\mathrm{ext}}=\{f(D'):D\in\mathcal F,\ \mathrm{TV}(D,D')\le a_*\}$, the parameter map is $L$-Lipschitz on $\mathcal F_{\mathrm{ext}}$: $\mathrm{loss}(\theta(D),\theta(D'))\le L\cdot\mathrm{TV}(D,D')$ for all $D,D'\in\mathcal F_{\mathrm{ext}}$;
--   2. the bias is at most $\Delta$: $\mathrm{loss}(\theta(D),g(\theta(f(D))))\le\Delta$ for all $D\in\mathcal F$;
--   3. $g$ is $K$-Lipschitz for the loss: $\mathrm{loss}(g(y),g(y'))\le K\,\mathrm{loss}(y,y')$ for all $y,y'$.
--
--   Let $A$ be a randomized algorithm on $n$ samples with seed law $\nu$ that is $(\alpha,\beta,\mathcal F_{\mathrm{ext}})$-high-confidence, and let $A'(X_1,\dots,X_n)=g(A(f(X_1),\dots,f(X_n)))$, run with the same seed. With $\varepsilon_*:=\log(1/\beta)/(4n)$, for every $\varepsilon>0$ with
--
--   $$
--   \varepsilon\cdot\max\big(1,\log(\varepsilon/a_*)\big)\le\varepsilon_*,
--   $$
--
--   the algorithm $A'$ is
--
--   $$
--   \big(\varepsilon,\ C^2(2K\alpha+\Delta),\ e^{-n\varepsilon},\ \mathcal F\big)\text{-TV-robust}.
--   $$
--
--   This is the paper's first main result in full generality (Theorem 1.9 is the case $f=g=\mathrm{id}$, $K=1$, $\Delta=0$): a high-confidence algorithm, after the pre- and post-processing, tolerates oblivious contamination up to $\varepsilon\approx\log(1/\beta)/n$, up to a logarithmic factor, with no change to the algorithm.
--
--   **Formalization Note** The algorithm is a jointly measurable map $\mathcal X^n\times\Omega\to\mathcal Y$ with a seed law $\nu$ on $\Omega$, and $\mathrm{loss}(\cdot,y)$ is measurable for each $y$, so the failure events are measurable. The condition on $\varepsilon$ is written $\beta\le\exp(-4n\varepsilon\max(1,\log(\varepsilon/a_*)))$ with $\beta\ge0$. There is no upper bound on $\varepsilon$, as on the page.
--
--   Differences from the source:
--   - reading: error O(Kα + Δ), with the constants of ≲ hidden (p.4) → error C² (2Kα + Δ), C ≥ 1 the constant of the loss's approximate triangle inequality; reason: the explicit value of the proof on p.18 (two triangle steps, then La* ≤ α); it implies the O-statement
--   - encoding: loss(y1, y2) ≲ loss(y1, y3) + loss(y3, y2), loss : Y × Y → R+ symmetric → hypotheses 0 ≤ loss, symmetry, loss y₁ y₂ ≤ C (loss y₁ y₃ + loss y₃ y₂) with 1 ≤ C; reason: a C-triangle inequality holds with max(C, 1); no loss is excluded
--   - encoding: ε · max(1, log(ε/a*)) ≤ ε* = log(1/β)/(4n) → 0 ≤ β and β ≤ exp(−4nε · max(1, log(ε/a))); reason: equivalent for β > 0 and n ≥ 1; at β = 0 (ε* = +∞) every ε is allowed, which Lean's log 0 = 0 would wrongly forbid; at n = 0, where the page divides by 0, it only asks β ≤ 1 and the conclusion is the trivial bound exp 0 = 1; at n = 0, where the page's ε* is undefined, it only asks β ≤ 1 and the conclusion is the trivial bound e^0 = 1
--   - encoding: threshold a* ∈ (0, 1/2) with a* ≤ α/L < 1/2 → 0 < a, a ≤ α / L, α / L < 1 / 2; reason: a* < 1/2 follows from a* ≤ α/L < 1/2
--   - generalization: computationally-efficient pre-processing f and efficient post-processing g → any measurable f : X → X and any g : Y → Y; reason: the efficiency qualifiers do not enter the statement's conclusion; efficient maps are such maps
--   - generalization: Δ := sup_{D ∈ F} loss(θ(D), g(θ(f(D)))) → any real Δ with loss(θ D, g(θ(f D))) ≤ Δ for all D ∈ F; reason: taking Δ equal to the supremum (when finite) gives the page's statement; an infinite supremum makes the page's error bound vacuous
--   - encoding: K the Lipschitzness parameter of g → 0 ≤ K with loss (g y) (g y') ≤ K * loss y y'; reason: a Lipschitz parameter is nonnegative
--   - encoding: randomized algorithm A : X^n → Y, probability over samples and the randomness of A; measurable events → A : (Fin n → X) → Ω → Y with Measurable (uncurry A), seed law ν, loss(·, y) measurable, f measurable; failure-set measure ≤ β; reason: the standing convention that algorithms and losses are measurable, so the success events are events
--   - encoding: θ : F → Y extended to F_ext → θ : ProbabilityMeasure X → Y; reason: only the values on F ∪ F_ext enter the statement
-- source:
--   Narayanan–Lee–Pensia, High Confidence Yields Outlier Robustness, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153), Theorem 4.2, p.17 (Assumption 4.1, p.17; Definitions 1.1, 1.3, 1.4, pp.4–5; full version of Theorem 1.9, p.6)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_HighConfRobust_IsHighConfidence
import Definitions.Def_HighConfRobust_IsTVRobust
import Definitions.Def_HighConfRobust_extFamily

namespace HighConfRobust

open MeasureTheory

/-- **Theorem 4.2** (computationally-efficient reduction from oblivious robustness, p.17).
Consider a statistical task on `X` with output space `Y`, parameter map `θ` and a nonnegative,
symmetric loss with the approximate triangle inequality `loss(y₁, y₂) ≤ C (loss(y₁, y₃) + loss(y₃, y₂))`.
Suppose Assumption 4.1 holds for the family `F` with pre-processing `f`, post-processing `g` and
threshold `a* ≤ α/L < 1/2`: `θ` is `L`-Lipschitz in TV on `F_ext = {f(D') : D ∈ F, TV(D, D') ≤ a*}`,
the bias `loss(θ(D), g(θ(f(D))))` is at most `Δ` on `F`, and `g` is `K`-Lipschitz for the loss.
If `A` is `(α, β, F_ext)`-high-confidence on `n` samples, then `A'(X₁, …, Xₙ) = g(A(f(X₁), …, f(Xₙ)))`
(same seed) is `(ε, C²(2Kα + Δ), e^{−nε}, F)`-TV-robust whenever
`ε · max(1, log(ε/a*)) ≤ ε* := log(1/β)/(4n)`.

Narayanan–Lee–Pensia, *High Confidence Yields Outlier Robustness: Consequences in Computational
Hardness, Privacy, and Replicability*, STOC 2027 submission manuscript, Nov. 3, 2026
(sha256 f0e4ec41…c370c153), Theorem 4.2, p.17 (with Assumption 4.1, p.17, and Definition 1.1,
p.4; full version of Theorem 1.9, p.6).

**Formalization Note**
* The error `O(Kα + Δ)` is the explicit `C²(2Kα + Δ)` of the proof (p.18), where `C ≥ 1` is the
  constant hidden in the loss's `≲` (p.4); `K ≥ 0` is the Lipschitz parameter of `g`.
* The condition `ε · max(1, log(ε/a*)) ≤ log(1/β)/(4n)` is written
  `β ≤ exp(−4nε · max(1, log(ε/a*)))`: the same condition for `β > 0` and `n ≥ 1`, and at `β = 0`
  (where `ε* = +∞`) it allows every `ε`. `ε > 0` has no upper bound, as on the page.
* `f` is any measurable map and `g` any map (the efficiency qualifiers play no role in the
  statement); `Δ` is any upper bound on the bias (the page's `Δ` is the supremum).
* The algorithm `A : (Fin n → X) → Ω → Y` with seed law `ν` is jointly measurable, and
  `loss(·, y)` is measurable: the standing convention that failure events are measurable.
* Distributions are `ProbabilityMeasure X`; `θ` is defined on all of them. `a* ∈ (0, 1/2)` is
  `0 < a*` (the bound `a* < 1/2` follows from `a* ≤ α/L < 1/2`). -/
theorem theorem_4_2 {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]
    (loss : Y → Y → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hloss_nonneg : ∀ y y', 0 ≤ loss y y') (hloss_symm : ∀ y y', loss y y' = loss y' y)
    (hloss_tri : ∀ y₁ y₂ y₃, loss y₁ y₂ ≤ C * (loss y₁ y₃ + loss y₃ y₂))
    (hloss_meas : ∀ y, Measurable fun z => loss z y)
    (F : Set (ProbabilityMeasure X)) (θ : ProbabilityMeasure X → Y)
    (f : X → X) (hf : Measurable f) (g : Y → Y) (a L K Δ α β ε : ℝ) (n : ℕ)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (A : (Fin n → X) → Ω → Y)
    (hA : Measurable (Function.uncurry A))
    (ha : 0 < a) (hL : 0 < L) (haα : a ≤ α / L) (hαL : α / L < 1 / 2)
    (hLip : ∀ E ∈ extFamily f hf a F, ∀ E' ∈ extFamily f hf a F,
      loss (θ E) (θ E') ≤ L * MarkovChainCLT.tvDist (E : Measure X) (E' : Measure X))
    (hΔ : ∀ D ∈ F, loss (θ D) (g (θ (D.map hf.aemeasurable))) ≤ Δ)
    (hK : 0 ≤ K) (hg : ∀ y y', loss (g y) (g y') ≤ K * loss y y')
    (hHC : IsHighConfidence loss θ A ν α β (extFamily f hf a F))
    (hβ : 0 ≤ β) (hε : 0 < ε)
    (hεβ : β ≤ Real.exp (-(4 * n * ε * max 1 (Real.log (ε / a))))) :
    IsTVRobust loss θ (fun S ω => g (A (f ∘ S) ω)) ν ε (C ^ 2 * (2 * K * α + Δ))
      (Real.exp (-(n * ε))) F := by sorry

end HighConfRobust
