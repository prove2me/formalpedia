-- Prove2me | Theorems.Thm_LinearZeroSumMG_theorem_1
-- name    : LinearZeroSumMG.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:55:01.119038+00:00
-- url     : https://prove2.me/theorems/5059950e-1012-4e53-b286-880de1f783ec
-- title:
--   Theorem 1, p.12 — OMNI-VI: (6) for all $k$, and $\sum_k(\overline V^k_1-\underline V^k_1)$, $\mathrm{Gap}(K)\lesssim\sqrt{d^3H^3T\iota^2}$, w.p. $1-p$
-- statement:
--   **Theorem 1 (Offline, simultaneous moves).** There are universal constants $c>0$ and $C>0$ such that the following holds.
--
--   Let $\mathcal S$ be a measurable state space, $\mathcal A$ a finite nonempty action set, $d,K,H\ge1$, and let a two-player zero-sum simultaneous-move episodic Markov game with horizon $H$ and rewards in $[-1,1]$ satisfy Assumption 1 with features in $\mathbb R^d$. Let $p\in(0,1)$, $T=KH$, $\iota=\log(2dT/p)$, and run Algorithm 1 (Optimistic Minimax Value Iteration) for $K$ episodes with:
--   1. bonus parameter $\beta=c\,dH\sqrt\iota$;
--   2. in Algorithm 2 (FIND_CCE), discretization $\varepsilon=1/(KH)$; for each episode $k$, an $\varepsilon$-net of minimum size of the class $\mathcal Q$ of (5) (functions $\Pi_H\{\langle w,\phi\rangle+\rho\beta\sqrt{\phi^\top A\phi}\}$ with $\|w\|\le2H\sqrt{dk}$, $\|A\|_F\le\beta^2\sqrt d$, $\rho=\pm1$); any admissible rounding rule into these nets; and any measurable rule selecting a coarse correlated equilibrium of the rounded matrix game (P1 maximizes the upper payoff, P2 minimizes the lower one);
--   3. initial states $x^k_1$ chosen arbitrarily, possibly depending on the past.
--
--   Let $\pi^k_h=\mathcal P_1\sigma^k_h$ and $\nu^k_h=\mathcal P_2\sigma^k_h$ be the marginals of the joint policy $\sigma^k$ computed in episode $k$, and $\mathrm{Gap}(K)=\sum_{k=1}^K[V^{*,\nu^k}_1(x^k_1)-V^{\pi^k,*}_1(x^k_1)]$. Then, with probability at least $1-p$, simultaneously
--   $$
--   V^{*,\nu^k}_1(x^k_1)-V^{\pi^k,*}_1(x^k_1)\le\overline V^k_1(x^k_1)-\underline V^k_1(x^k_1)+\frac8K\quad\forall k\in[K],\tag{6}
--   $$
--   $$
--   \sum_{k=1}^K\big[\overline V^k_1(x^k_1)-\underline V^k_1(x^k_1)\big]\le C\sqrt{d^3H^3T\iota^2},\tag{7}
--   $$
--   $$
--   \mathrm{Gap}(K)\le C\sqrt{d^3H^3T\iota^2}.\tag{8}
--   $$
--
--   The total duality gap grows like $\sqrt T$, independently of the number of states and actions; (6) also yields a computable certificate $\overline V^k_1-\underline V^k_1$ of each episode's gap, which converts the bound into a sample-complexity (PAC) guarantee.
--
--   **Formalization Note** The constants $c$ and $C$ are quantified before every other object. The three bounds are asserted on one event, and "with probability at least $1-p$" bounds the outer measure of its complement by $p$.
--
--   Differences from the source:
--   - encoding: "there exists a constant c > 0" and ≲ ("x ≥ Cy holds for a universal absolute constant C > 0", §2.1, p.5) → ∃ c > 0, ∃ C > 0 quantified before the state space, the game, d, K, H, p and the rules; reason: §2.1 defines ≲ with a universal absolute constant; the universal c is the stronger order and the proof gives it (β ≍ dH√ι)
--   - encoding: "with probability at least 1 − p" → the outer measure of the set of sample points where the bound fails is at most p; reason: no measurability of the event is needed; same statement when it is measurable
--   - generalization: the standing assumption of §2.2.1 that an NE exists and its value is unique → no Nash-equilibrium assumption; reason: Theorem 1 and its proof never use V* or Q*; Lemma 5's (b), (ii) follow from Q^{π,*} ≤ Q^{π,ν} ≤ Q^{*,ν}, which needs no NE; every game with an NE is covered
--   - generalization: "an arbitrary initial state x^k_1 is chosen" (p.9) → x^k_1 is any random state measurable with respect to everything observed before episode k (IsOmniRun); reason: an adaptively chosen initial state covers every fixed sequence of initial states
--   - reading: Assumption 1's normalization ‖μ_h(𝒮)‖ ≤ √d (p.7) → ‖(∫ v dμ_h^{(i)})_{i∈[d]}‖ ≤ √d for every measurable v : 𝒮 → [−1, 1] (IsLinearMG); reason: read literally as a bound on the vector of net masses, the assumption does not give ‖∫ V dμ_h‖ ≤ H√d for |V| ≤ H, which the proofs of Lemmas 3 and 7 use, and Lemma 7 is then false (d = 3, two states, φ(s) = (0.7, 0.5, 0), φ(t) = (0.7, −0.5, 0), μ = ((δ_s+δ_t)/1.4, δ_s − δ_t, 7(δ_s − δ_t)), θ = (0, 1, 0), H = 2: ‖μ(𝒮)‖ ≈ 1.43 ≤ √3 but ‖w_1‖ ≥ 7 > 4√3); the reading implies the printed bound (v ≡ 1) and is implied by the total-variation bound
--   - reading: "let σ̃(x) be the CCE" (Algorithm 2, line 3, p.11) → every Borel-measurable rule cce mapping a pair of payoff matrices to one of its CCEs (IsCCERule), fixed in advance; reason: the definite article and Lemma 2's proof ("Fix a pair (Q̃, Q̰) in the ε-net … let σ̃(x) be the CCE") require a rule fixed before the run; the statement holds for every such rule
--   - reading: "Pick a pair (Q̃, Q̰) in 𝒬_ε × 𝒬_ε satisfying ‖Q̃ − Q̄^k_h‖_∞ ≤ ε and ‖Q̰ − Q̲^k_h‖_∞ ≤ ε" (Algorithm 2, line 2, p.11) → every measurable rounding rule that, given k, h and the parameters (w̄^k_h, (Λ^k_h)⁻¹), (w̲^k_h, (Λ^k_h)⁻¹) of Q̄^k_h and Q̲^k_h, returns such a pair whenever both lie in 𝒬 (IsRoundingRule); reason: "pick" allows any qualifying pair; one pair must serve every state x (Lemma 2's proof rounds Q̄^k_{h+1} once); any choice that is a function of FIND_CCE's input pair is such a rule
--   - reading: "Let 𝒬_ε be a fixed ε-covering of 𝒬" (p.11) → for each episode k ∈ [K], an ε-net of the class 𝒬 of (5) for that k (‖w‖ ≤ 2H√(dk)), contained in 𝒬 and of minimum cardinality (IsMinEpsNet); reason: Lemma 2's proof uses |𝒬_ε × 𝒬_ε| = (𝒩_ε)², the covering number; an arbitrary cover (e.g. 𝒬 itself) breaks the union bound; 𝒬 depends on k through ‖w‖ ≤ 2H√(dk)
--   - encoding: feature map, policies, CCE rule and rounding with no measurability stated; finite action set → φ jointly measurable, policies measurable in the state, CCE rule and rounding rule Borel measurable, A with its discrete σ-algebra; reason: without measurability the expectations ℙ_h V and the conditional laws of the analysis are undefined; these conditions exclude only such cases
--   - encoding: d, K, H the feature dimension, number of episodes and horizon → 1 ≤ d, 1 ≤ K, 1 ≤ H as hypotheses; reason: ι = log(2dT/p), ε = 1/(KH) and 8/K are undefined otherwise; nondegeneracy only
--   - encoding: V^{π,ν}_h, Q^{π,ν}_h as expected sums of rewards along a trajectory; V^{*,ν} = max_π, V^{π,*} = min_ν (p.6) → backward Bellman recursion for a fixed pair; best responses as ⨆/⨅ over measurable stochastic Markov policies; reason: for a fixed Markov policy pair the trajectory expectation equals the recursion; same instances
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, Theorem 1, pp.12–13; (4), p.9

import Mathlib
import Definitions.Def_LinearZeroSumMG_IsLinearMG
import Definitions.Def_LinearZeroSumMG_IsEpsNet
import Definitions.Def_LinearZeroSumMG_IsOmniRun
import Definitions.Def_LinearZeroSumMG_dualityGap
import Definitions.Def_LinearZeroSumMG_iota

open MeasureTheory ProbabilityTheory

namespace LinearZeroSumMG

/-- **Theorem 1 (Offline, Simultaneous Moves).**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, Theorem 1, pp.12–13: "Under
Assumption 1, there exists a constant `c > 0` such that the following holds for each fixed
`p ∈ (0, 1)`. Set `β = cdH√ι` with `ι := log(2dT/p)` in Algorithm 1, and set `ε = 1/(KH)` in
Algorithm 2. Then with probability at least `1 − p`, Algorithm 1 satisfies the bounds
`V^{*,ν^k}_1(x^k_1) − V^{π^k,*}_1(x^k_1) ≤ V̄^k_1(x^k_1) − V̲^k_1(x^k_1) + 8/K, ∀k ∈ [K]` (6)
`∑_{k=1}^K [V̄^k_1(x^k_1) − V̲^k_1(x^k_1)] ≲ √(d³H³Tι²)`; (7)
consequently, we have `Gap(K) ≲ √(d³H³Tι²)`. (8)"

There are universal constants `c > 0` and `C > 0` such that: for every measurable state space `S`,
finite nonempty action set `A`, `d, K, H ≥ 1`, game satisfying Assumption 1 (rewards in `[−1, 1]`),
`p ∈ (0, 1)`, measurable CCE rule, family of minimum-size `ε`-nets `𝒬_ε` of the classes `𝒬` of (5)
(one per episode `k ∈ [K]`), rounding rule into them, with `β = c·dH√ι`, `ι = log(2dT/p)`,
`T = KH`, `ε = 1/(KH)`, and every run of Algorithm 1 for `K` episodes, the outer probability that
(6) fails for some `k ∈ [K]`, or `∑_{k=1}^K [V̄^k_1(x^k_1) − V̲^k_1(x^k_1)] > C√(d³H³Tι²)`, or
`Gap(K) > C√(d³H³Tι²)`, is at most `p`.

**Formalization Note**
- `≲` is "`≤ C ·` for a universal absolute constant `C > 0`" (§2.1, p.5); `c` and `C` are chosen
  before every other object, so neither depends on the game, `d`, `H`, `K`, `p` or the rules.
- The three bounds hold together on one event of probability at least `1 − p`.
- `π^k = 𝒫₁σ^k` and `ν^k = 𝒫₂σ^k` are the marginal policies whose duality gap is measured; `V̄`, `V̲` use
  the joint `σ^k` itself.
- The initial states may be chosen adaptively; the NE assumption of §2.2.1 is not needed and not
  made. -/
theorem theorem_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
    ∀ {S A : Type} [MeasurableSpace S] [MeasurableSpace A] [DiscreteMeasurableSpace A]
      [Fintype A] [Nonempty A] (d K : ℕ) (G : MarkovGame S A) (φ : S → A → A → Fin d → ℝ)
      (θ : ℕ → Fin d → ℝ) (μh : ℕ → Fin d → SignedMeasure S) (p : ℝ)
      (cce : (A → A → ℝ) → (A → A → ℝ) → (A × A → ℝ)) (N : ℕ → Finset (S → A → A → ℝ))
      (round : RoundRule S A d) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›) (x : ℕ → ℕ → Ω → S)
      (a b : ℕ → ℕ → Ω → A),
      1 ≤ d → 1 ≤ K → 1 ≤ G.H → IsLinearMG G φ θ μh → 0 < p → p < 1 → IsCCERule cce →
      (∀ k ∈ Finset.Icc 1 K, IsMinEpsNet (N k)
        (QClass φ G.H (c * d * G.H * Real.sqrt (iota d K G.H p)) k) (1 / ((K : ℝ) * G.H))) →
      IsRoundingRule φ G.H (c * d * G.H * Real.sqrt (iota d K G.H p)) (1 / ((K : ℝ) * G.H))
        N K round →
      IsOmniRun μ 𝓕 G ⟨φ, c * d * G.H * Real.sqrt (iota d K G.H p), cce, round⟩ K x a b →
      let P : OmniParams S A d := ⟨φ, c * d * G.H * Real.sqrt (iota d K G.H p), cce, round⟩
      μ {ω | ¬ (
        -- (6)
        (∀ k ∈ Finset.Icc 1 K,
          bestV1 G (nuK G P (fun τ i => x τ i ω) (fun τ i => a τ i ω) (fun τ i => b τ i ω) k)
              1 (x k 1 ω)
            - bestV2 G (piK G P (fun τ i => x τ i ω) (fun τ i => a τ i ω) (fun τ i => b τ i ω) k)
              1 (x k 1 ω)
          ≤ VUp G P (fun τ i => x τ i ω) (fun τ i => a τ i ω) (fun τ i => b τ i ω) k 1 (x k 1 ω)
            - VLo G P (fun τ i => x τ i ω) (fun τ i => a τ i ω) (fun τ i => b τ i ω) k 1 (x k 1 ω)
            + 8 / (K : ℝ)) ∧
        -- (7)
        ∑ k ∈ Finset.Icc 1 K,
            (VUp G P (fun τ i => x τ i ω) (fun τ i => a τ i ω) (fun τ i => b τ i ω) k 1 (x k 1 ω)
              - VLo G P (fun τ i => x τ i ω) (fun τ i => a τ i ω) (fun τ i => b τ i ω) k 1
                (x k 1 ω))
          ≤ C * Real.sqrt ((d : ℝ) ^ 3 * (G.H : ℝ) ^ 3 * ((K : ℝ) * G.H) *
              iota d K G.H p ^ 2) ∧
        -- (8)
        dualityGap G P K (fun τ i => x τ i ω) (fun τ i => a τ i ω) (fun τ i => b τ i ω)
          ≤ C * Real.sqrt ((d : ℝ) ^ 3 * (G.H : ℝ) ^ 3 * ((K : ℝ) * G.H) *
              iota d K G.H p ^ 2))} ≤ ENNReal.ofReal p := by sorry

end LinearZeroSumMG
