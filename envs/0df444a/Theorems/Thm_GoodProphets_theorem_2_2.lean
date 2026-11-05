-- Prove2me | Theorems.Thm_GoodProphets_theorem_2_2
-- name    : GoodProphets.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:26:18.616557+00:00
-- url     : https://prove2.me/theorems/954f2dc7-9780-435e-bc2a-fcddce669d27
-- title:
--   Theorem 2.2 — some algorithm has loss at most $M(\beta,\lambda,\delta,\epsilon,\ell)$, independent of $T$, when the horizon is revealed $T^{1/2+\epsilon}$ periods before the end
-- statement:
--   Fix $\epsilon>0$. Then there is a constant $M(\beta,\lambda,\delta,\epsilon,\ell)$ with the following property. For every instance of the objective $f_{\vec N}$, with any number $k$ of types, any $\ell\ge1$ actions per type and any constraint data $A,D,\vec B,\vec c_1,\vec c_2$, and for every tie-breaking rule $\sigma$, there is an online algorithm $\mathrm{ALG}$ such that
--
--   $$
--   L_{\mathrm{ALG}}=\mathbb E\Big[f_{\vec N}(\vec x^{\mathrm{ALG}})-\mathrm{OPT}(\vec N)\Big]\ \le\ M(\beta,\lambda,\delta,\epsilon,\ell)
--   $$
--
--   whenever all of the following hold:
--
--   1. $f_{\vec N}$ is real-valued and satisfies property (i) of Proposition 1 with $\lambda$ and property (ii) with $\delta$;
--   2. $\sigma$ satisfies Assumption 2 with $\delta$;
--   3. the types arrive i.i.d. from an unknown distribution $\vec p$ with $p_\theta\ge\beta>0$ for every $\theta$ (Assumption 1);
--   4. the horizon $T$, unknown in advance, is revealed at a heads-up time $\hat T$ with $T-\hat T>T^{1/2+\epsilon}$ (Assumption 3).
--
--   The algorithm does not know $\vec p$, $\beta$, $\lambda$, $\delta$ or $\hat T$, and it learns $T$ only after $\hat T$.
--
--   This is the main result of the paper. A heads-up of order $T^{1/2+\epsilon}$ periods before the end suffices for a loss bounded independently of the horizon. Section 4 of the paper shows that a heads-up of order $\sqrt T$ does not suffice.
--
--   **Formalization Note** The order of the quantifiers carries the content. $M$ is chosen before the instance, so it depends only on $\beta,\lambda,\delta,\epsilon,\ell$: not on $k$, the constraint data, $\vec p$, $T$ or $\hat T$. The algorithm is chosen after the instance and $\sigma$ but before $\beta,\lambda,\delta,\vec p,T,\hat T$. The paper's remark "we assume without loss of generality that $\hat T\ge T/2$" (p.8) is not a hypothesis: every heads-up time allowed by Assumption 3 is covered.
--
--   Differences from the source:
--   - reading: Assumption 2: a tie-breaking rule "that maintains λ-Lipschitz continuity in the right-hand side" → Selection I σ δ: σ(N, y) ∈ argmin_{x≥y} f_N, with |σ(N, y) − σ(N′, y)|_∞ ≤ δ|N − N′|_∞ for Σ N = Σ N′; reason: the proofs of Lemmas 3.3 and 3.5 use the constant δ of Proposition 1 (ii) for the selected solutions; a λ-Lipschitz rule satisfies this with max(λ, δ)
--   - reading: OPT(N) = min_x f_N(x) → the minimum over real (fractional) x ≥ 0 with Σⱼ x_θj = N_θ; reason: the paper's convention (p.10: L = E[OPT^T − OPT^1] since x^ALG(0) = 0); the fractional optimum is the smaller one, so the bound is the stronger
--   - reading: Proposition 1 (i): f_N λ-Lipschitz, no norm named → λ-Lipschitz in the ℓ1 norm; reason: the proof's "loss in any period is bounded by 2λ" (p.13) is the ℓ1 distance of one action; ℓ1 is the weakest hypothesis among the standard norms
--   - encoding: Proposition 1 (ii) "for any y, any N and N′" → only when both feasible sets {x ≥ y : Σⱼ x_θj = N_θ} are non-empty (likewise in Assumption 2); reason: the argmin is undefined when a feasible set is empty, and the unguarded property is unsatisfiable for k ≥ 2 (proved in the sanity file); the cited Mangasarian–Shiau theorem assumes non-empty solution sets
--   - encoding: f_N(x) treated as a real number → the hypothesis I.Bounded: the inner LP over z is bounded below for N ≥ 0 and Σⱼ x_θj = N_θ; reason: excludes only instances where f_N = −∞ and the paper's objects are undefined
--   - encoding: every type has a non-empty action set (p.7: one of the actions must be played) → 0 < ℓ; reason: with ℓ = 0 no algorithm exists; the paper's ℓ counts the actions of a type
--   - encoding: ALG an online algorithm; T revealed at the heads-up T̂ → π : List (Fin k × Fin ℓ) → Fin k → Option ℕ → PMF (Fin ℓ), receiving some T exactly in periods t > T̂; reason: the paper's information structure: past arrivals and actions, the current type, and T after T̂ only
--   - encoding: T̂ random, a priori unknown and independent of the arrivals (Assumption 3) → T and T̂ fixed, the algorithm chosen before them; reason: the bound holds uniformly in T and T̂, so it holds after averaging over any T̂ independent of the arrivals; the algorithm cannot depend on T̂
--   - encoding: the expectation E in (1) → a finite sum over trajectories (θ⃗, a⃗) weighted by ∏ᵢ p_{θᵢ} π(aᵢ | history, θᵢ, info); reason: the exact law of the arrivals and the algorithm's randomization; no instance changes
--   - generalization: Proposition 1 (i), (ii) and Assumption 2 for any y and any N, N′ → LipHyp, StabHyp, Selection, I.Bounded only for y ≥ 0, N, N′ ≥ 0; reason: weaker hypotheses, so a stronger theorem; only y ≥ 0 and N ≥ 0 occur in the paper, and an instance satisfying the printed properties satisfies these
--   - generalization: "we assume without loss of generality that T̂ ≥ T/2" (p.8) → no such hypothesis: every T̂ with T − T̂ > T^{1/2+ε}; reason: Assumption 3 does not contain it; the case T̂ ≥ T/2 is an instance
-- source:
--   S. Banerjee and D. Freund, Good prophets know when the end is near, Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript, sha256 2cfd1ada…2c46), Theorem 2.2, p.9; Assumptions 1–3 and Proposition 1, pp.7–8; loss (1), p.8 (proof pp.12–14)

import Mathlib
import Definitions.Def_GoodProphets_LipHyp
import Definitions.Def_GoodProphets_Selection
import Definitions.Def_GoodProphets_loss

namespace GoodProphets

/-- **Theorem 2.2** (Banerjee & Freund, *Good prophets know when the end is near*, Management
Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript), p.9): "There exists an algorithm
ALG and a constant `M(β, λ, δ, ε, ℓ)`, independent of `T`, such that `L_ALG ≤ M(β, δ, λ, ε, ℓ)`."

For every `ε > 0` there is a function `M(β, λ, δ, ℓ)` such that for every instance of the objective
`f_N` (any `k`, constraint data `A, D, B⃗, c⃗₁, c⃗₂`) and every tie-breaking rule `σ` there is an
online algorithm `π` with the following property: for all `β, λ, δ`, every arrival distribution `p`
with `p_θ ≥ β > 0` (Assumption 1), every horizon `T` and heads-up time `T̂` with
`T − T̂ > T^{1/2+ε}` (Assumption 3), if `f_N` is real-valued, satisfies Proposition 1 (i) with `λ`
and (ii) with `δ`, and `σ` satisfies Assumption 2 with `δ`, then `L_ALG ≤ M(β, λ, δ, ℓ)`.

**Formalization Note** The quantifier order carries the content: `M` is chosen before the instance
(so it depends only on `β, λ, δ, ε, ℓ`), and `π` is chosen before `β, λ, δ, p, T, T̂`, so the
algorithm does not know them; it learns `T` only in the periods after `T̂` (`Policy`,
`horizonInfo`). `T̂ ≥ T/2` is not assumed (the paper calls it w.l.o.g., p.8). The loss is against
the fractional clairvoyant optimum over `x ≥ 0`. `0 < ℓ` (every type has an action) is needed for a
policy to exist. -/
theorem theorem_2_2 (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ → ℝ → ℝ → ℕ → ℝ,
      ∀ (k ℓ r m : ℕ) (I : Instance k ℓ r m)
        (σ : (Fin k → ℝ) → (Fin k → Fin ℓ → ℝ) → (Fin k → Fin ℓ → ℝ)), 0 < ℓ →
      ∃ π : Policy k ℓ,
        ∀ (β lam δ : ℝ) (p : Fin k → ℝ) (T Th : ℕ),
          I.Bounded → LipHyp I lam → StabHyp I δ → Selection I σ δ →
          0 < β → (∀ θ, β ≤ p θ) → ∑ θ, p θ = 1 →
          (T : ℝ) ^ ((1 : ℝ) / 2 + ε) < (T : ℝ) - Th →
          loss I π p T Th ≤ M β lam δ ℓ := by sorry

end GoodProphets
