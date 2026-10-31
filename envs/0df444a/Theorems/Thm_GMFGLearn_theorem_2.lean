-- Prove2me | Theorems.Thm_GMFGLearn_theorem_2
-- name    : GMFGLearn.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:56:15.482242+00:00
-- url     : https://prove2.me/theorems/30a15e0e-9ad7-4bd9-8a2f-d10bb3e9c55e
-- title:
--   Theorem 2 — convergence and complexity of GMF-V (corrected: equilibrium selected by $\Gamma_1$, $\operatorname{diam}(\mathcal S\times\mathcal A)$ in $K$, sample bound (23), Bellman equation)
-- statement:
--   Let $\mathcal S$ and $\mathcal A$ be finite nonempty metric spaces and consider a GMFG on them. Let $\Gamma_1(\mathcal L)_s=\mathrm{argmax\text{-}e}(Q^\star_{\mathcal L}(s,\cdot))$, $\Gamma(\mathcal L)=\Gamma_2(\Gamma_1(\mathcal L),\mathcal L)$, and assume Assumption 1 for this $\Gamma_1$ (constant $d_1$), Assumption 2 (constants $d_2,d_3$), and $d:=d_1d_2+d_3\in(0,1)$. Write
--   $$K=K_{\epsilon,\eta}=\Big\lceil2\max\big\{(\eta\epsilon/c)^{-1/\eta},\ \log_d\big(\epsilon/\max\{\operatorname{diam}(\mathcal S\times\mathcal A),c\}\big)+1\big\}\Big\rceil,\quad\epsilon_k=(k+1)^{-(1+\eta)},\quad\delta_k=\delta/K.$$
--
--   1. **Convergence.** There is a constant $C_0$, depending only on the model and on $d_1,d_2,d_3$, with the following property. Let $\epsilon,\delta>0$, $\eta\in(0,1]$, $\varphi>0$ and $c\ge c'\ge\log(1/\epsilon)/\varphi$ with $c'>0$; let $f$ map $\mathbb R^{\mathcal A}$ to probability distributions on $\mathcal A$ with $f\in\mathcal F_{c,c'}$; let $S_\epsilon$ be an $\epsilon$-net with action gap $\varphi$ and $\mathrm{Proj}_{S_\epsilon}$ a $d_{TV}$-nearest-point projection onto it; let $\mathcal L_0$ be arbitrary and $\mathcal L^\star$ a fixed point of $\Gamma$. Let $\hat Q_k$ be random Q-estimates on a probability space and $\mathcal L_k$ the GMF-V iterates $\mathcal L_{k+1}=\mathrm{Proj}_{S_\epsilon}(\Gamma_2(\pi_k,\mathcal L_k))$, $\pi_k(s)=f(\hat Q_k(s,\cdot))$. If for every $k<K$
--   $$\mathbb P\big(\|\hat Q_k-Q^\star_{\mathcal L_k}\|_\infty>\epsilon_k\big)\le2\delta_k,$$
--   then
--   $$\mathbb P\big(W_1(\mathcal L_K,\mathcal L^\star)>C_0\epsilon\big)\le2\delta .$$
--   2. **Sample complexity.** For $\epsilon>0$, $\delta\in(0,1]$, $\eta\in(0,1]$, $c>0$ and $C^{(i)},\alpha^{(i)}_1,\alpha^{(i)}_2\ge0$, the total sample count $T=\sum_{k=0}^{K-1}T(\epsilon_k,\delta_k)$ of (22) satisfies
--   $$T\le\sum_{i=1}^m2^{\alpha^{(i)}_2}C^{(i)}K^{2\alpha^{(i)}_1+1}(K/\delta)^{\alpha^{(i)}_3}\big(\log(K/\delta)\big)^{\alpha^{(i)}_2+\alpha^{(i)}_4}.$$
--
--   This is the main result of the paper: a learner of single-agent Q-functions, combined with smoothing and projection, finds the mean-field equilibrium to accuracy $O(\epsilon)$ with high probability, at an explicit sample cost.
--
--   **Formalization Note** $\mathbb P$ of the failure events is the outer measure, so no measurability of the run is assumed. The sample space is any probability space. The run is a function of the random estimates.
--
--   Differences from the source:
--   - correction: L⋆ "the population state-action pair in a stationary NE" → L⋆ a fixed point of Γ = Γ₂(Γ₁(·),·), the equilibrium whose policy is Γ₁(L⋆); reason: with S = {0}, A = {0,1}, P ≡ δ₀, r ≡ 0, L⋆ = δ₀⊗δ₀ is an NE but the exact learner gives L_K = δ₀⊗uniform and W₁(L_K, L⋆) = 1/2 for every K ≥ 1
--   - correction: K_{ϵ,η} with max{diam(S)diam(A), c} → max{diam(S×A), c}, diam in the ℓ₂ product cost; reason: S = {0,1}, A = {0}, r ≡ 0, P(1|s,a,L) = 1/4 + µ_L(1)/2 (d = 1/2, µ⋆(1) = 1/2) with ϵ = min(1/2, 1/(8C₀)), c = c′ = ϵ/4, φ = 4log(1/ϵ)/ϵ, η = 1 gives K = 1 and W₁(L₁, L⋆) = 1/4 > C₀ϵ with probability 1
--   - correction: T ≤ Σ_i 2^{α₂}/(2α₁+1) C K^{2α₁+1}(K/δ)^{α₃}(log(K/δ))^{α₂+α₄} → the same bound without the factor 1/(2α₁+1), for δ ∈ (0,1] and C, α₁, α₂ ≥ 0; reason: m = 1, C = 1, α = (1,0,0,0), η = 1 give T = K(K+1)(2K+1)/6 > K³/3; for δ > 1, log(1/δ) < 0 and (22) is undefined or the bound fails (α = (0,1,0,0), δ = K ≥ 2); negative exponents break it (α₁ = −1)
--   - correction: Bellman equation printed with max_{a′} before Σ_{s′} → Q⋆ the solution of Q(s,a) = r(s,a) + γ Σ_{s′} P(s′|s,a) max_{a′} Q(s′,a′); reason: the page calls the solution the optimal Q-function with V⋆(s) = max_a Q⋆(s,a), and the printed equation does not have that solution: S = {0,1,2}, A = {0,1}, s = 0 moves to 1 or 2 with probability 1/2 each, 1 and 2 are absorbing, r(1,0) = r(2,1) = 1, other rewards 0; the printed solution has Q(0,a) = γ(1+γ)/(2(1−γ)), the optimal value at 0 is γ/(1−γ)
--   - reading: f_{c,c′} : ℝⁿ → ℝⁿ with "f_{c,c′} ⊆ F_{c,c′}" → f : ℝ^A → P(A) whose probability vectors form a member of F_{c,c′}; reason: π_k(s) = f(Q̂(s,·)) must be a randomized action, and ⊆ between a map and a set is read as membership
--   - reading: one C^{(i)}_M in (23) while M = M_{L_k} varies, and T_{M_{L_k}}(δ_k, ϵ_k) → one family C^{(i)} for every k, and T(ϵ_k, δ_k); reason: (23) has a single C^{(i)}_M; Algorithm 2 line 3 uses T_{M_{L_k}}(ϵ_k, δ_k)
--   - generalization: "Alg has a value-based guarantee" → the per-iteration hypothesis P(‖Q̂_k − Q⋆_{L_k}‖∞ > ϵ_k) ≤ 2δ_k for random estimates on any probability space; reason: this is the only use the proof makes of the guarantee (p.22); a learner with the guarantee run with T_{M_{L_k}}(ϵ_k, δ_k) samples at step k satisfies it
--   - generalization: finite S ⊆ ℝ^d, A ⊆ ℝ^p → finite nonempty metric spaces with Borel σ-fields, S×A with the cost √(d_S² + d_A²); reason: §2.1 states compact metric spaces and §4 adds finiteness; Euclidean subsets are an instance
--   - generalization: "the constant C_0 is independent of δ, ϵ and η" → C₀ also independent of c, c′, φ, f, the net, the projection, L₀, L⋆ and the sample space; reason: (43) has no such dependence; a C₀ uniform in more parameters gives the source's C₀ for each choice of them
--   - encoding: L̃_{k+1} obtained from the simulator G(s, π_k, L_k) → L̃_{k+1} = Γ₂(π_k, L_k); reason: the proof uses exactly this (W₁(L̃_{k+1}, L⋆) = W₁(Γ₂(π_k, L_k), …), p.22)
--   - encoding: d = d₁d₂ + d₃ ∈ [0,1) → d ∈ (0,1); reason: log_d in K is undefined at d = 0
--   - encoding: reward law R(s,a,L) ∈ P([0,Rmax]) → measurable mean reward r̄(s,a,L) ∈ [0,Rmax]; reason: Q⋆_L and Γ depend on R only through its mean, and every such r̄ is the mean of R = δ_r̄
--   - encoding: Proj_{S_ϵ}(L) = argmin d_TV(L^{(i)}, L) → any d_TV-nearest point of the net; reason: the argmin may have ties, broken arbitrarily
--   - encoding: "with probability at least 1 − 2δ" → the outer measure of the failure event is ≤ 2δ; reason: the same statement, with no measurability of the run assumed
--   - encoding: Condition 2 with δ := ∞ when all x_j are equal → f(x) = argmax-e(x) when all x_j are equal; reason: 2n exp(−c′·∞) = 0 for c′ > 0
--   - encoding: there exist a positive function φ(ϵ) and an ϵ-net S_ϵ → any positive number φ and any finite net with the two properties of p.12 at level ϵ, φ; reason: Algorithm 2 takes S_ϵ as input, and the theorem uses only these two properties
-- source:
--   Guo, Hu, Xu, Zhang, A General Framework for Learning Mean-Field Games, arXiv:2003.06069v3, Theorem 2, p.13; Algorithm 2, p.13; proof of Theorem 2, pp.22–23

import Mathlib
import Definitions.Def_GMFGLearn_GMFV

open MeasureTheory

namespace GMFGLearn

/-- **Theorem 2 (convergence and complexity of GMF-V).** Guo–Hu–Xu–Zhang, *A General Framework for
Learning Mean-Field Games*, arXiv:2003.06069v3, Theorem 2, p.13: "Assume the same assumptions as
Theorem 1, and f_{c,c′} ⊆ F_{c,c′}. Suppose that Alg has a value-based guarantee with parameters
{C^{(i)}_M, α^{(i)}_1, α^{(i)}_2, α^{(i)}_3, α^{(i)}_4}_{i=1}^m. For any ϵ, δ > 0, set δ_k = δ/K_{ϵ,η},
ϵ_k = (k + 1)^{−(1+η)} for some η ∈ (0,1] (k = 0,...,K_{ϵ,η} − 1), and c ≥ c′ ≥ log(1/ϵ)/φ(ϵ). Then
with probability at least 1 − 2δ, W_1(L_{K_{ϵ,η}}, L⋆) ≤ C_0ϵ. Here K_{ϵ,η} := ⌈2 max{(ηϵ/c)^{−1/η},
log_d(ϵ/max{diam(S)diam(A), c}) + 1}⌉ … and the constant C_0 is independent of δ, ϵ and η.
Moreover, the total number of samples T = Σ_{k=0}^{K_{ϵ,η}−1} T_{M_{L_k}}(δ_k, ϵ_k) is bounded by
T ≤ Σ_{i=1}^m 2^{α^{(i)}_2}/(2α^{(i)}_1 + 1) C^{(i)}_M K^{2α^{(i)}_1+1}_{ϵ,η} (K_{ϵ,η}/δ)^{α^{(i)}_3}
(log(K_{ϵ,η}/δ))^{α^{(i)}_2+α^{(i)}_4}. (23)"

**Formalization Note**
* Finite compact metric `S`, `A` (§4, p.10), `d = d₁d₂ + d₃ ∈ (0,1)` (`log_d` needs `d > 0`),
  Assumptions 1 and 2 with `Γ₁ = argmax-e ∘ Q⋆` (p.11).
* `L⋆` is the fixed point of `Γ = Γ₂(Γ₁(·),·)`, i.e. the equilibrium whose policy is the selected
  `Γ₁(L⋆)` (correction C1: another equilibrium can be at a fixed positive distance from every
  GMF-V limit).
* `K_{ϵ,η}` uses `diam(S × A)` in the ℓ₂ product cost (correction C2: with one action
  `diam(S)diam(A) = 0`, and the printed `K` can equal 1 while `W₁(L₁, L⋆) = 1/4 > C₀ϵ`).
* The sample bound (ii) is stated without the factor `1/(2α₁ + 1)`, for `δ ∈ (0,1]` and
  `C, α₁, α₂ ≥ 0` (correction C3: with `m = 1`, `C = 1`, `α = (1,0,0,0)`, `η = 1`, the left side is
  `K(K+1)(2K+1)/6 > K³/3`).
* `Q⋆` solves the Bellman optimality equation with the maximum inside the sum, against the printed
  `γ max_{a′} Σ_{s′}` (see `GMFGLearn.FiniteMDP`).
* `f` maps `ℝ^A` to `P(A)`; its probability vectors form a member of `F_{c,c′}`.
* "Alg has a value-based guarantee" enters as the per-iteration hypothesis
  `P(‖Q̂_k − Q⋆_{L_k}‖_∞ > ϵ_k) ≤ 2δ_k` for the random estimates `Qhat k` on any probability space
  `Ω`; the failure event is bounded in (outer) measure.
* `C₀` is chosen before `ϵ, δ, η, c, c′, φ, f`, the net, the projection, `L₀`, `L⋆` and the run, so
  it depends only on the model and `d₁, d₂, d₃`. -/
theorem theorem_2 {S A : Type*}
    [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S] [Nonempty S] [Fintype S]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nonempty A] [Fintype A]
    (M : GMFG S A) (d₁ d₂ d₃ : ℝ)
    (hA1 : Assumption1 M.finiteGamma1 d₁) (hA2 : Assumption2 M d₂ d₃)
    (hd_pos : 0 < d₁ * d₂ + d₃) (hd_lt : d₁ * d₂ + d₃ < 1) :
    (∃ C₀ : ℝ, ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ η ∈ Set.Ioc (0 : ℝ) 1,
      ∀ c c' φ : ℝ, 0 < c' → c' ≤ c → 0 < φ → Real.log (1 / ε) / φ ≤ c' →
      ∀ f : (A → ℝ) → ProbabilityMeasure A,
        (fun x a => ((f x : ProbabilityMeasure A) : Measure A).real {a}) ∈ FSet c c' →
      ∀ net : Finset (ProbabilityMeasure (S × A)), IsEpsNet M net ε φ →
      ∀ proj : ProbabilityMeasure (S × A) → ProbabilityMeasure (S × A), IsProj net proj →
      ∀ L₀ Lstar : ProbabilityMeasure (S × A), M.Gamma M.finiteGamma1 Lstar = Lstar →
      ∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
        (Qhat : ℕ → Ω → S → A → ℝ),
        (∀ k < Kiter ε η c (d₁ * d₂ + d₃) (diamSA S A),
          volume {ω | epsK η k <
              supErr (Qhat k ω) (M.optQL (gmfvRun M f proj L₀ Qhat k ω))} ≤
            ENNReal.ofReal (2 * (δ / Kiter ε η c (d₁ * d₂ + d₃) (diamSA S A)))) →
        volume {ω | C₀ * ε <
            W1 dSA (gmfvRun M f proj L₀ Qhat (Kiter ε η c (d₁ * d₂ + d₃) (diamSA S A)) ω)
              Lstar} ≤ ENNReal.ofReal (2 * δ)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ η ∈ Set.Ioc (0 : ℝ) 1, ∀ c : ℝ, 0 < c →
      ∀ (m : ℕ) (C α₁ α₂ α₃ α₄ : Fin m → ℝ),
        (∀ i, 0 ≤ C i ∧ 0 ≤ α₁ i ∧ 0 ≤ α₂ i) →
        ∑ k ∈ Finset.range (Kiter ε η c (d₁ * d₂ + d₃) (diamSA S A)),
            sampleBound C α₁ α₂ α₃ α₄ (epsK η k)
              (δ / Kiter ε η c (d₁ * d₂ + d₃) (diamSA S A)) ≤
          ∑ i, 2 ^ α₂ i * C i *
            (Kiter ε η c (d₁ * d₂ + d₃) (diamSA S A) : ℝ) ^ (2 * α₁ i + 1) *
            ((Kiter ε η c (d₁ * d₂ + d₃) (diamSA S A) : ℝ) / δ) ^ α₃ i *
            Real.log ((Kiter ε η c (d₁ * d₂ + d₃) (diamSA S A) : ℝ) / δ) ^ (α₂ i + α₄ i)) := by sorry

end GMFGLearn
