-- Prove2me | Theorems.Thm_GOLiQ_theorem_2
-- name    : GOLiQ.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:45.597426+00:00
-- url     : https://prove2.me/theorems/9c8144db-58a6-40cd-af67-99f7982c8612
-- title:
--   Theorem 2 — regret of suboptimality: $\mathbb E\|x_k-x^*\|^2\le Ck^{-\beta}$ and (16)
-- statement:
--   Suppose Assumption 3 holds. Let $x_{k+1}=\Pi_{\mathcal B}(x_k-\eta_kH_k)$ from a deterministic $x_1\in\mathcal B$, with step sizes $\eta_k>0$, $\eta_k\to0$, and estimators $H_k$ determined by the first $k$ iterations. If there is a constant $K_3\ge1$ such that for all $k$
--
--   1. $(1+1/k)^\beta\le1+\frac{K_0}2\eta_k$,
--   2. $B_k\le\frac{K_0}8k^{-\beta}$,
--   3. $\eta_k\mathcal V_k\le K_3k^{-\beta}$,
--
--   where $0<\beta\le1$, then there is a constant $C\ge 8K_3/K_0$ such that for all $k\ge1$
--   $$\mathbb E[\|x_k-x^*\|^2]\le Ck^{-\beta},\tag{15}$$
--   and, for the queue run in cycles of lengths $D_k\ge1$ under these $x_k$ and $M$ the constant of Lemma 1,
--   $$R_2(L)\le CK_1\sum_{k=1}^L\Big(\frac{D_k}{\lambda(\bar p)}+M\Big)k^{-\beta}=O\Big(\sum_{k=1}^LD_kk^{-\beta}\Big).\tag{16}$$
--
--   This is a convergence rate for projected SGD with biased gradients, turned into a regret bound.
--
--   Differences from the source:
--   - encoding: fee p > 0, service and arrival rates, the box [µ̲, µ̄] × [p̲, p̄] → 0 < µ̲ < µ̄, 0 < p̲ < p̄ and 0 < λ(p̄); reason: the fee is p > 0 (p.10) and rates are positive; λ′, c′ and ∇f on B are determined only when the intervals are nondegenerate
--   - encoding: λ and c continuously differentiable, with derivatives λ′ and c′ → C¹ on the closed intervals [p̲, p̄] and [µ̲, µ̄], λ′ and c′ the derivatives within them; reason: only values on the box enter the model
--   - encoding: U and V independent i.i.d. sequences with unit means; Z drawn in Algorithm 1 → nonnegative Uₙ, Vₙ and the draws Zₖ (uniform on {1, 2}) on one probability space, all mutually independent; reason: Uₙ/λ and Vₙ/µ are times; statements that do not mention Z do not depend on it
--   - encoding: x = (µ, p) with the Euclidean norm → a point of EuclideanSpace ℝ (Fin 2), coordinate 0 = µ, 1 = p; reason: the norm of p.12
--   - encoding: ∇f in Assumption 3 and x* = (µ*, p*) optimal → a field g with HasGradientWithinAt f (g x) B x for x ∈ B, and x* ∈ B a minimizer of f on B; reason: Lemma 5 gives differentiability; Assumption 3(a) already forces x* to be the minimizer
--   - reading: the per-cycle indexing of §3.3 with leftovers, recursions (6)–(7) and the price rule of p.15 → one global customer index j = N_{k−1} + n; customer 0 arrives at time 0 to an empty system; customer j pays p_{c(j−1)}, c(i) the last cycle that started strictly before the arrival of customer i; reason: it reproduces (6)–(7) with W₀¹ = 0, Q₁ = 0, and charges the first new arrival of cycle k the old fee p_{k−1}
--   - reading: 𝓕ₖ, the σ-algebra including all events in the first k − 1 iterations → 𝓕ₖ = σ(Uⱼ, Vⱼ : j ≤ N_{k−1}; Z₁, …, Z_{k−1}); an admissible policy has each xₖ ∈ B and 𝓕ₖ-measurable; reason: the primitives of every customer who entered service in cycles 1, …, k − 1 and the coordinate draws (p.68: xₖ ∈ 𝓕ₖ)
--   - encoding: cycle lengths Dₖ → deterministic Dₖ ≥ 1; reason: a cycle serves at least one customer (Lemma 1 assumes Dₖ ≥ 1)
--   - reading: M, the constant of Lemma 1 → any M for which the bounds of Lemma 1 hold for the queue in question; reason: Lemma 1 supplies such an M; the statement holds for each of them
--   - encoding: Π_B, the projection onto B → the coordinatewise clamp to [µ̲, µ̄] × [p̲, p̄]; reason: the Euclidean projection onto a box
--   - reading: the SGD framework of §3.2 with 'ηₖ → 0 is the step size' → x_{k+1} = Π_B(xₖ − ηₖHₖ) from a deterministic x₁ ∈ B, ηₖ > 0, ηₖ → 0, each Hₖ 𝓕_{k+1}-measurable; reason: the iteration of p.12; Hₖ is computed from the data of iteration k
--   - generalization: Assumption 3 with Assumptions 1–2 standing → no Assumption 2 hypothesis; (16) holds for every M (with any η) satisfying Lemma 1's bounds for this queue; reason: Assumption 2 is used only to produce M through Lemma 1
--   - generalization: a constant C with (15) and (16) → C chosen before M and uniform in it; reason: the same C serves every valid M
--   - generalization: (16) → also asserts that each Tₖ is integrable; reason: implied by Lemma 1's bounds; excludes junk values in R₂(L)
--   - encoding: expectations of nonnegative quantities → lower Lebesgue integrals in [0, ∞]; reason: a finite bound then also asserts finiteness, and no junk value 0 arises for a non-integrable quantity
--   - encoding: W∞(µ, p), the steady-state waiting time → Loynes' supremum sup_{n≥0} Σ_{j=1}^n (Vⱼ/µ − Uⱼ/λ(p)) on the primitives; reason: it has the stationary law; it is the coupling from the past of p.58
--   - encoding: f of (2), through the steady-state queue length Q∞(µ, p) → f defined by (5), h₀λ(p)(E[W∞(µ, p)] + 1/µ) + c(µ) − pλ(p); reason: the paper's own identity (5) (Little's law, p.13) for every (µ, p) ∈ B; Q∞ is not used elsewhere
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, Theorem 2, p.28; §3.2, p.12

import Mathlib
import Definitions.Def_GOLiQ_Model
import Definitions.Def_GOLiQ_Primitives
import Definitions.Def_GOLiQ_Model_objective
import Definitions.Def_GOLiQ_Assumption3
import Definitions.Def_GOLiQ_CycleSystem
import Definitions.Def_GOLiQ_Primitives_info
import Definitions.Def_GOLiQ_Model_MomentBound
import Definitions.Def_GOLiQ_Model_regret
import Definitions.Def_GOLiQ_estimatorBias
import Definitions.Def_GOLiQ_estimatorVariance

open MeasureTheory Filter Topology

namespace GOLiQ

/-- **Theorem 2 (regret of suboptimality)** (Chen, Liu, Hong, arXiv:2009.02911v3, p.28): suppose
Assumption 3 holds. If there is a constant `K₃ ≥ 1` such that for all `k`

(a) `(1 + 1/k)^β ≤ 1 + (K₀/2)ηₖ`,
(b) `Bₖ ≤ (K₀/8)k^{−β}`,
(c) `ηₖ𝒱ₖ ≤ K₃k^{−β}`,

where `0 < β ≤ 1` and `ηₖ → 0` is the step size, then there is a constant `C ≥ 8K₃/K₀` such that for
all `k ≥ 1`

`E[‖xₖ − x*‖²] ≤ Ck^{−β}`,    (15)

and as a consequence

`R₂(L) ≤ CK₁ Σ_{k=1}^L (Dₖ/λ(p̄) + M) k^{−β} = O(Σ_{k=1}^L Dₖk^{−β})`.    (16)

**Formalization Note.** The iteration is the SGD recursion of §3.2 (p.12),
`xₖ₊₁ = Π_B(xₖ − ηₖHₖ)` from a deterministic `x₁ ∈ B`, with any estimators `Hₖ` determined by the
first `k` iterations (`𝓕ₖ₊₁`-measurable). `Bₖ`, `𝒱ₖ` are (4) with `∇f` the gradient field `g` of
Assumption 3. `R₂(L)` is computed for the queue run in cycles of lengths `Dₖ ≥ 1` under these
`xₖ`, and `M` is any constant for which the bounds of Lemma 1 hold for this queue (with any `η`).
`C` does not depend on `M`. Part (16) also asserts that each `Tₖ` is integrable. The "explicit
expression (34)" of `C` is not part of the statement. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω)
    (g : Point → Point) (xstar : Point) (K₀ K₁ : ℝ) (h3 : Assumption3 M Pr g xstar K₀ K₁)
    (D : ℕ → ℕ) (hD : ∀ k : ℕ, 1 ≤ k → 1 ≤ D k)
    (step : ℕ → ℝ) (hstep : ∀ k : ℕ, 1 ≤ k → 0 < step k) (hstep0 : Tendsto step atTop (𝓝 0))
    (x H : ℕ → Ω → Point) (hx₁ : ∃ x₁ ∈ M.box, ∀ ω, x 1 ω = x₁)
    (hx : ∀ k : ℕ, 1 ≤ k → ∀ ω, x (k + 1) ω = M.proj (x k ω - step k • H k ω))
    (hH : ∀ k : ℕ, 1 ≤ k → Measurable[Pr.info D (k + 1)] (H k))
    (β K₃ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hK₃ : 1 ≤ K₃)
    (ha : ∀ k : ℕ, 1 ≤ k → (1 + 1 / (k : ℝ)) ^ β ≤ 1 + K₀ / 2 * step k)
    (hb : ∀ k : ℕ, 1 ≤ k →
      estimatorBias Pr (Pr.info D) g x H k ≤ ENNReal.ofReal (K₀ / 8 * (k : ℝ) ^ (-β)))
    (hc : ∀ k : ℕ, 1 ≤ k →
      ENNReal.ofReal (step k) * estimatorVariance Pr H k ≤ ENNReal.ofReal (K₃ * (k : ℝ) ^ (-β))) :
    ∃ C : ℝ, 8 * K₃ / K₀ ≤ C ∧
      (∀ k : ℕ, 1 ≤ k →
        ∫⁻ ω, ‖x k ω - xstar‖ₑ ^ 2 ∂Pr.P ≤ ENNReal.ofReal (C * (k : ℝ) ^ (-β))) ∧
      ∀ η Mc : ℝ, M.MomentBound Pr D x η Mc →
        (∀ k : ℕ, 1 ≤ k → Integrable (fun ω => (M.system Pr D x ω).length k) Pr.P) ∧
        ∀ L : ℕ, 1 ≤ L →
          M.suboptRegret Pr D x xstar L ≤
            C * K₁ * ∑ k ∈ Finset.Icc 1 L, ((D k : ℝ) / M.lam M.pHi + Mc) * (k : ℝ) ^ (-β) := by sorry

end GOLiQ
