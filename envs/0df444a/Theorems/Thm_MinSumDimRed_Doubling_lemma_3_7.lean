-- Prove2me | Theorems.Thm_MinSumDimRed_Doubling_lemma_3_7
-- name    : MinSumDimRed.Doubling.lemma_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:36:08.89664+00:00
-- url     : https://prove2.me/theorems/5e73b1cb-cc15-4a03-9f60-b2d935ec96ca
-- title:
--   Lemma 3.7 — from random clusters to all partitions: with probability $\ge 4/5$, both bounds hold for every partition at once
-- statement:
--   **Lemma 3.7** (From random clusters to all partitions, p. 15). Let $X = \{p_0, \dots, p_{n-1}\} \subseteq \mathbb R^d$ ($n$ distinct points), $k \in \mathbb N$, $\mathrm{OPT}$ the optimal min-sum $k$-clustering cost of $X$, $\varepsilon > 0$, and $f : \mathbb R^d \to \mathbb R^t$ a random map on a probability space. Let $A, \Gamma$ be reals with $A \le (1 + \varepsilon)^2$ and $A\Gamma \le \frac{\varepsilon}{2k}\mathrm{OPT}$. Suppose that for every random subset $C \subseteq X$ which may depend on $f$, with probability at least $4/5$,
--   $$\mathrm{cost}(C) \le A\big(\mathrm{cost}(f(C)) + \Gamma\big) \quad\text{and}\quad \mathrm{cost}(f(C)) \le A\big(\mathrm{cost}(C) + \Gamma\big).$$
--   Then, with probability at least $4/5$, for every $k$-partition $P$ of $X$ simultaneously,
--   $$(1 - \varepsilon)\,\mathrm{cost}(P) \le (1 + \varepsilon)^2\,\mathrm{cost}(f(P)), \qquad \mathrm{cost}(f(P)) \le (1 + \varepsilon)^3\,\mathrm{cost}(P).$$
--
--   Differences from the source:
--   - generalization: every k-partition P = {P_1, …, P_k} of X → every labelling σ : Fin n → Fin k (part i = σ⁻¹(i)); parts may be empty; reason: every partition of X into k nonempty parts is such a labelling, so the for-all conclusion over more partitions specializes to the source; the paper itself allows partitions into at most k parts in §4
--   - encoding: cost(f(P)) over the multisets f(P_i) → MinSumFPT.labCost (imgDist f p) σ = Σ_i Σ_{x,y: σx=σy=i} ‖f(p x) − f(p y)‖; reason: sums over the points of X, so coinciding images are counted with multiplicity exactly as the p. 3 multisets
--   - encoding: a finite point set X ⊆ ℝ^d with n = |X| points → an injective family p : Fin n → EuclideanSpace ℝ (Fin d), X = Set.range p; reason: same instances: injectivity makes the n indexed points distinct, so |X| = n
--   - encoding: OPT, the optimal min-sum k-clustering cost of X (cost of an optimal k-partition P*) → MinSumFPT.optCost (eucl p) k = infimum of labCost over labellings σ : Fin n → Fin k; reason: for 1 ≤ k ≤ n it equals the minimum over partitions into exactly k nonempty parts (splitting a part never increases the cost); for k > n, where no such partition exists, it is 0, and for k = 0 (not an instance) it is 0; P* itself appears only in the proof
--   - encoding: random map f : ℝ^d → ℝ^t; random subset C ⊆ X which may depend on f → f : Ω → Pt d → Pt t with each ω ↦ f ω x measurable (IsRandomMap); C : Ω → Finset (Fin n) with measurable membership events (IsRandomSubset), on one probability space (Ω, μ) of arbitrary type; no independence between C and f; reason: a random object is a random variable on the probability space carrying f
--   - reading: ε (no range stated in Lemma 3.7) → 0 < ε; reason: Section 3 works with 0 < ε throughout (Definition 3.1: 'Given 0 < ε ≤ 1/2'); the proof uses only ε ≥ 0
--   - encoding: ε/(2k) at k = 0 → ε / (2 * (k : ℝ)) with Lean's x/0 = 0; reason: k = 0 is not an instance; there the conclusion is vacuous for n ≥ 1 (no labelling Fin n → Fin 0) and trivial for n = 0
--   - encoding: with probability at least p / Pr[event] ≤ q → p ≤ μ.real {ω | …} / μ.real {ω | …} ≤ q on a probability measure μ; reason: μ.real is the (outer) measure as a real number; no measurability of the event is presupposed, and for measurable events it is the probability
-- source:
--   Asaf Dallal, Robert Krauthgamer, Dimension Reduction and Coresets for Min-Sum k-Clustering, arXiv:2610.38920 (version of November 2, 2026, SHA-256 13a9281e…), p. 15 (PDF 15), Lemma 3.7 (proof p. 16)

import Mathlib
import Definitions.Def_MinSumFPT_labCost
import Definitions.Def_MinSumDimRed_Doubling_Costs
import Definitions.Def_MinSumDimRed_Doubling_Random

open MeasureTheory ProbabilityTheory

namespace MinSumDimRed.Doubling

/-- Lemma 3.7 (From random clusters to all partitions), p. 15. Let `X = {p 0, …, p (n-1)} ⊆ ℝ^d`
(`n` distinct points), `k ∈ ℕ`, `OPT` the optimal min-sum `k`-clustering cost of `X`, `0 < ε`, and
`f` a random map `ℝ^d → ℝ^t` on a probability space. Suppose that for every random subset `C ⊆ X`
(which may depend on `f`), with probability at least `4/5`,
`cost(C) ≤ A (cost(f(C)) + Γ)` and `cost(f(C)) ≤ A (cost(C) + Γ)`, where `A ≤ (1 + ε)^2` and
`A Γ ≤ (ε / 2k) OPT`. Then, with probability at least `4/5`, for every `k`-partition `P` of `X`
(a labelling `σ : Fin n → Fin k`, empty parts allowed),
`(1 - ε) cost(P) ≤ (1 + ε)^2 cost(f(P))` and `cost(f(P)) ≤ (1 + ε)^3 cost(P)`. -/
theorem lemma_3_7 {d t n : ℕ} (k : ℕ) (p : Fin n → Pt d) (hp : Function.Injective p)
    (ε : ℝ) (hε : 0 < ε)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → Pt d → Pt t) (hf : IsRandomMap f)
    (A Γ : ℝ) (hA : A ≤ (1 + ε) ^ 2)
    (hAΓ : A * Γ ≤ ε / (2 * (k : ℝ)) * MinSumFPT.optCost (eucl p) k)
    (hC : ∀ C : Ω → Finset (Fin n), IsRandomSubset C →
      (4 / 5 : ℝ) ≤ μ.real {ω |
        setCost p (C ω) ≤ A * (imgSetCost (f ω) p (C ω) + Γ) ∧
        imgSetCost (f ω) p (C ω) ≤ A * (setCost p (C ω) + Γ)}) :
    (4 / 5 : ℝ) ≤ μ.real {ω | ∀ σ : Fin n → Fin k,
      (1 - ε) * MinSumFPT.labCost (eucl p) σ ≤
          (1 + ε) ^ 2 * MinSumFPT.labCost (imgDist (f ω) p) σ ∧
        MinSumFPT.labCost (imgDist (f ω) p) σ ≤ (1 + ε) ^ 3 * MinSumFPT.labCost (eucl p) σ} := by sorry

end MinSumDimRed.Doubling
