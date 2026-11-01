-- Prove2me | Theorems.Thm_OfflineToOnline_theorem_2
-- name    : OfflineToOnline.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:36.271292+00:00
-- url     : https://prove2.me/theorems/e2fc8357-ae8f-442b-915f-c3902654c336
-- title:
--   Theorem 2 — robust, Blackwell-reducible greedy algorithms yield online $\gamma$-regret $O(D(\boldsymbol p)N\delta\sqrt{\log(d_{\mathrm{payoff}})T})$
-- statement:
--   Let $\textsc{Offline-IG}(\mathcal C,\mathcal F,\mathcal D,\Theta)$ be an instance of Algorithm 1 with $N$ subproblems and payoff dimension $d_{\mathrm{payoff}}$ whose local update is driven by seeds of law $\nu$. Suppose that
--
--   1. it is an extended $(\gamma,\delta)$-robust approximation (Definition 6) for some $\gamma\in(0,1)$ and $\delta\ge0$, and
--   2. it is Blackwell reducible (Definition 7) via a Blackwell game $(\Theta,\mathcal Y,\boldsymbol p)$ and a synthetic adversary $\mathrm{AdvB}$.
--
--   Consider the full-information online version of problem (1) against an oblivious adversary $f_1,\dots,f_T\in\mathcal F$, and let $z_t$ be the point played by Online-IG (Algorithm 2) in round $t$. Then:
--
--   **(i)** for every $T\ge1$, every $g\ge0$ and every measurable payoff-based Blackwell algorithm $\mathrm{AlgB}$ with actions in $\Theta$ that approaches the nonnegative orthant at horizon $T$ with $\ell_\infty$ rate $g$,
--
--   $$
--   \gamma\sum_{t=1}^Tf_t(\hat z)-\sum_{t=1}^T\mathbb E\big[f_t(z_t)\big]\ \le\ \delta\,N\,T\,g\qquad\text{for every }\hat z\in\mathcal C ;
--   $$
--
--   **(ii)** there is one absolute constant $c$ such that for every Blackwell game $(\Theta,\mathcal Y,\boldsymbol p)$ ($\Theta,\mathcal Y$ compact convex, $\Theta$ nonempty, $\boldsymbol p$ biaffine, the nonnegative orthant response-satisfiable) and every $T\ge1$ there is a measurable payoff-based Blackwell algorithm $\mathrm{AlgB}$ for $(\Theta,\mathcal Y,\boldsymbol p)$ with actions in $\Theta$, depending only on the game and $T$, such that for every instance as above that is Blackwell reducible via this game, Online-IG with $\mathrm{AlgB}$ satisfies
--
--   $$
--   \gamma\sum_{t=1}^Tf_t(\hat z)-\sum_{t=1}^T\mathbb E\big[f_t(z_t)\big]\ \le\ c\,D(\boldsymbol p)\,N\,\delta\,\sqrt{\log(d_{\mathrm{payoff}})\,T}\qquad\text{for every }\hat z\in\mathcal C ,
--   $$
--
--   that is, $\gamma\text{-regret}(\textsc{Online-IG})=O\big(D(\boldsymbol p)N\delta\sqrt{\log(d_{\mathrm{payoff}})T}\big)$.
--
--   The expectation is over the randomness of the local updates. The theorem turns any offline greedy $\gamma$-approximation that is robust and Blackwell reducible into a no-$\gamma$-regret online algorithm with $O(\sqrt T)$ regret, which the paper applies to submodular maximization, product ranking and reserve prices.
--
--   Differences from the source:
--   - generalization: F is closed under addition (standing assumption, p.10) → not assumed; reason: together with f : D → [0,1] it forces F ⊆ {0}; the proof does not use it; every instance of the source is covered
--   - generalization: δ ∈ ℝ₊ (Definition 6: δ > 0) → δ ≥ 0; reason: covers every δ > 0
--   - generalization: AlgB a Blackwell algorithm with the approachability bound of Theorem 1 (Remark 1) → clause (i): any measurable payoff-based AlgB approaching the orthant at horizon T with any rate g ≥ 0, with the bound δ·N·T·g of the last display of the proof (p.22); reason: with Theorem 1's g it gives clause (ii); clause (ii) states the printed O(·) bound
--   - reading: Online-IG runs in polynomial time → not formalized; Online-IG is the explicit procedure of Algorithm 2 (onlineIG); reason: the paper fixes no computational model; each round makes N calls to AlgB, Local-update and Payoff
--   - reading: O(D(p) N δ √(log(d_payoff) T)) → c · payoffDiam p Θ Y · N · δ · √(log d · T) with one c chosen before every parameter; reason: the strongest reading of O(·)
--   - reading: Online-IG initializes z_t^(0) ∈ C in each round → z_t^(0) = z₀, the initial point of the Offline-IG instance, in every round; reason: the robustness of Definition 6 is a property of the runs of Algorithm 1 from its initial point
--   - reading: noisy update parameters θ̃_t^(i) of Definition 6 (dependence unspecified) → adapted measurable functions of the seeds, the slack condition required on every seed realization; reason: a variant of Algorithm 1 chooses parameters from the random past of its run; Online-IG is such a variant
--   - encoding: γ-regret(ALG) = max over f_1..f_T of E[γ max_{z∈C} Σ f_t(z) − Σ f_t(z_t)] (Definition 2) → the bound for every f_1..f_T ∈ F and every ẑ ∈ C; reason: equivalent whenever the maximum exists; avoids a supremum over C
--   - encoding: Local-update : Θ × D → Δ(C) → a measurable map update(θ, z, ω) of independent seeds ω with law ν, expectation under the product law seedLaw; reason: every kernel into a standard Borel space has this representation
--   - encoding: no measurability stated → f ∈ F, Payoff (in (θ, z)), Local-update and AlgB (at each round) measurable; reason: needed for E[f_t(z_t)] to exist; excludes only undefined cases
--   - encoding: AlgB a Blackwell algorithm against player 2 strategies; h(·) : ℕ → ℝ₊ → a deterministic payoff-based strategy that may depend on T, approaching against every sequence in Y; a real h ≥ 0 per T; reason: Algorithm 2 feeds AlgB its own past parameters and the realized payoffs; only h(T) enters Definition 6
--   - encoding: the Blackwell game's action space X = Θ; rounds 1..T and subproblems 1..N → Θ nonempty; T ≥ 1; 0-indexed rounds and subproblems; types in arbitrary universes; reason: a game needs a player 1 action, otherwise no Blackwell algorithm exists
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Theorem 2, p.20 (proof pp.20–22; Algorithm 2, p.21; Definition 2, p.11)

import Mathlib
import Definitions.Def_OfflineToOnline_IsBiaffineOn
import Definitions.Def_OfflineToOnline_payoffDiam
import Definitions.Def_OfflineToOnline_IsResponseSatisfiable
import Definitions.Def_OfflineToOnline_IsNoisyPolicy
import Definitions.Def_OfflineToOnline_seedLaw
import Definitions.Def_OfflineToOnline_IsExtRobust
import Definitions.Def_OfflineToOnline_IGInstance
import Definitions.Def_OfflineToOnline_runPoints
import Definitions.Def_OfflineToOnline_payoffPlay
import Definitions.Def_OfflineToOnline_Approaches
import Definitions.Def_OfflineToOnline_orthant
import Definitions.Def_OfflineToOnline_IsBlackwellReducible
import Definitions.Def_OfflineToOnline_onlineIG

universe u v

namespace OfflineToOnline

/-- **Theorem 2** (Full information offline-to-online transformation). Suppose an instance of
Offline-IG`(C, F, D, Θ)` is an extended `(γ, δ)`-robust approximation (`γ ∈ (0, 1)`, `δ ≥ 0`) and is
Blackwell reducible via the game `(Θ, Y, p)` and the synthetic adversary `AdvB`. Then Online-IG
with a Blackwell algorithm `AlgB` has, against every oblivious adversary `f_1, …, f_T ∈ F`,

(i) for every `T ≥ 1`, every `g ≥ 0` and every measurable payoff-based `AlgB` with actions in `Θ`
that approaches the nonnegative orthant at horizon `T` with ℓ∞ rate `g`:
`γ ∑_t f_t(ẑ) − ∑_t E[f_t(z_t)] ≤ δ N T g` for every `ẑ ∈ C`;

(ii) γ-regret `O(D(p) N δ √(log(d_payoff) T))`: there is one absolute constant `c` such that for
every Blackwell game `(Θ, Y, p)` (compact convex, `Θ` nonempty, `p` biaffine, orthant
response-satisfiable) and every `T ≥ 1` there is a measurable payoff-based Blackwell algorithm
`AlgB` for `(Θ, Y, p)` with actions in `Θ` (chosen from the game and `T` only, as "a Blackwell
algorithm for (X, Y, p)" on p.20) such that every robust instance reducible via `(Θ, Y, p)` gives
`γ ∑_t f_t(ẑ) − ∑_t E[f_t(z_t)] ≤ c · D(p) N δ √(log(d_payoff) · T)` for every `ẑ ∈ C`.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Theorem 2, p.20 (proof pp.20–22; Algorithm 2, p.21; Definition 2, p.11).

Formalization Note: `z_t = runPoints I (onlineIG I A f) t N ω` is the point played in round `t`
on the seed realization `ω`, whose law is `seedLaw ν T N`. "γ-regret ≤ B" (Definition 2) is stated as
`γ ∑_t f_t(ẑ) − ∑_t E[f_t(z_t)] ≤ B` for every `f_1, …, f_T ∈ F` and every `ẑ ∈ C`. The O(·) is
one constant `c` chosen before every parameter. "Runs in polynomial time" is not formalized:
Online-IG is the explicit procedure `onlineIG` of Algorithm 2. `log` is the natural logarithm;
`D(p)` is `payoffDiam`. -/
theorem theorem_2 :
    (∀ {D : Type u} {Ω : Type v} [MeasurableSpace D] [MeasurableSpace Ω] {m k d : ℕ}
        (I : IGInstance D Ω m d) (ν : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure ν] (γ δ : ℝ), 0 < γ → γ < 1 → 0 ≤ δ →
        IsExtRobust I ν γ δ →
        ∀ (Y : Set (Fin k → ℝ)) (p : (Fin m → ℝ) → (Fin k → ℝ) → (Fin d → ℝ))
          (AdvB : D → (D → ℝ) → (Fin k → ℝ)), IsBlackwellReducible I Y p AdvB →
        ∀ T : ℕ, 1 ≤ T → ∀ g : ℝ, 0 ≤ g → ∀ A : PayoffStrategy m d, (∀ t, Measurable (A t)) →
          Approaches p I.Θ Y (orthant d) A T g →
        ∀ f : Fin T → D → ℝ, (∀ t, f t ∈ I.F) → ∀ zhat ∈ I.C,
          γ * ∑ t, f t zhat -
              ∑ t, ∫ ω, f t (runPoints I (onlineIG I A f) t I.N ω) ∂(seedLaw ν T I.N) ≤
            δ * I.N * T * g) ∧
    (∃ c : ℝ, ∀ {m k d : ℕ} (Θ : Set (Fin m → ℝ)) (Y : Set (Fin k → ℝ))
        (p : (Fin m → ℝ) → (Fin k → ℝ) → (Fin d → ℝ)),
        IsCompact Θ → Convex ℝ Θ → Θ.Nonempty → IsCompact Y → Convex ℝ Y → IsBiaffineOn Θ Y p →
        IsResponseSatisfiable Θ Y p (orthant d) →
        ∀ T : ℕ, 1 ≤ T → ∃ A : PayoffStrategy m d,
          (∀ (t : ℕ) (h : Fin t → (Fin m → ℝ) × (Fin d → ℝ)), A t h ∈ Θ) ∧
          (∀ t, Measurable (A t)) ∧
          ∀ {D : Type u} {Ω : Type v} [MeasurableSpace D] [MeasurableSpace Ω]
            (I : IGInstance D Ω m d), I.Θ = Θ → ∀ (ν : MeasureTheory.Measure Ω)
            [MeasureTheory.IsProbabilityMeasure ν] (γ δ : ℝ), 0 < γ → γ < 1 → 0 ≤ δ →
            IsExtRobust I ν γ δ →
            ∀ AdvB : D → (D → ℝ) → (Fin k → ℝ), IsBlackwellReducible I Y p AdvB →
            ∀ f : Fin T → D → ℝ, (∀ t, f t ∈ I.F) → ∀ zhat ∈ I.C,
              γ * ∑ t, f t zhat -
                  ∑ t, ∫ ω, f t (runPoints I (onlineIG I A f) t I.N ω) ∂(seedLaw ν T I.N) ≤
                c * payoffDiam p Θ Y * I.N * δ * Real.sqrt (Real.log d * T)) := by sorry

end OfflineToOnline
