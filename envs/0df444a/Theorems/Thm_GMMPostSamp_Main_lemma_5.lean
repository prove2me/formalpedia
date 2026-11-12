-- Prove2me | Theorems.Thm_GMMPostSamp_Main_lemma_5
-- name    : GMMPostSamp.Main.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:28:55.152775+00:00
-- url     : https://prove2.me/theorems/0f996269-16b8-4b27-a068-d787ab23c671
-- title:
--   Lemma 5 — an estimator as in Proposition 4 plus a δ/2-sampler for the lifted posterior solve Problem 1 with O(ndk) extra time
-- statement:
--   There are an admissible program $Q$ and a universal $C>0$ such that the following holds for all $k,d,n\ge1$, $\sigma>0$, $0<a\le A$, $\alpha\in[a,A]^k$, $\delta\in(0,\frac12)$ and $r\in(0,\frac16)$. Let $\bar\theta\sim\mathrm{Est}(x_{[n]})$ be any randomized estimator and $E$ an event over $(\theta^\star,\iota^\star,x_{[n]},\bar\theta)$ of probability at least $1-\delta^2/6$ on which $\bar\theta\in\Theta$, $\min_{\theta'\in\mathrm{Orb}(\bar\theta)}\|\theta'-\theta^\star\|_2\le r$ and the sets $\Phi_c(B)$ are pairwise disjoint (the guarantee of Proposition 4 invoked with $\delta\leftarrow\delta^2/6$), $B=\{\theta\in\Theta:\|\theta-\bar\theta\|_2\le3r\}$. Let $\mathcal A$ be a randomized algorithm that, whenever $E$ holds, takes $(x_{[n]},\bar\theta)$ and outputs $(\hat\theta,\hat c)\in B\times S_k$ with
--   $$\mathrm{TV}\big(\mathrm{Law}(\hat\theta,\hat c),\tilde\Pi_B\big)\le\frac\delta2.$$
--   Then the algorithm "draw $\bar\theta$, call $\mathcal A$, run $Q$ on $(k,d,n,\sigma,\alpha,x_{[n]},\hat\theta,\hat c)$" solves Problem 1, and $Q$ halts within $C\,ndk+C$ steps on every run for every $\hat\theta\in\Theta$, $\hat c\in S_k$.
--
--   **Formalization Note.** The estimator and $\mathcal A$ are Markov kernels (the output laws of the two calls); the label law at $x$ is the law of $Q$'s decoded output under $\mathrm{Est}(x)\otimes\mathcal A\otimes$ tapes.
--
--   Differences from the source:
--   - generalization: (θ̄, B) defined as in Proposition 4 invoked with δ ← δ²/6, E the event of Proposition 4 → any randomized estimator (Markov kernel from x_[n]) and any event E of probability ≥ 1 − δ²/6 on which θ̄ ∈ Θ, the orbit of θ̄ is within r of θ⋆ and the relabelled 3r-balls are disjoint; reason: LearnGMM with its event E is such a pair; the proof uses only these properties
--   - generalization: A an algorithm → A any Markov kernel from (x_[n], θ̄) to Θ × S_k; reason: the output law of any algorithm is such a kernel
--   - reading: there is an algorithm that solves Problem 1 by calling Proposition 4 and A once each, and using O(ndk) additional time → the composition θ̄ ∼ Est(x), (θ̂, ĉ) ∼ A(x, θ̄), then a fixed admissible program Q on (k, d, n, σ, α, x, θ̂, ĉ) halting within C·ndk + C steps on every run (θ̂ ∈ Θ), solves Problem 1; reason: the additional work is the program Q; the two calls are the given estimator and A
--   - encoding: P[TV(Law(ι), π) ≤ δ] ≥ 1 − δ → Model-1 (outer) measure of {x : TV > δ} ≤ δ; reason: Problem 1 as in the Machine definition
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), p. 19, Lemma 5

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_PolyVoting_dirichletMeasure
import Definitions.Def_GMMPostSamp_Main_Toolkit
import Definitions.Def_GMMPostSamp_Main_Model
import Definitions.Def_GMMPostSamp_Main_Machine

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-- Lemma 5 (p. 19): let `θ̄` be produced from `x_[n]` by an estimator (any randomized
estimator, e.g. LearnGMM) satisfying the guarantee of Proposition 4 invoked with `δ ← δ²/6`
on an event `E`, and let `A` be a randomized algorithm that, whenever `E` holds, takes
`(x_[n], θ̄)` (hence `B`) and outputs `(θ̂, ĉ) ∈ B × S_k` with `TV(Law(θ̂, ĉ), Π̃_B) ≤ δ/2`. Then
calling the estimator and `A` once each, followed by a program `Q` taking `C·ndk + C` steps,
solves Problem 1. -/
theorem lemma_5 : ∃ Q : Machine.Program, Machine.Admissible Q ∧ ∃ C : ℝ, 0 < C ∧
    ∀ k d n : ℕ, 1 ≤ k → 1 ≤ d → 1 ≤ n → ∀ (σ a A δ r : ℝ) (α : Fin k → ℝ),
      0 < σ → 0 < a → a ≤ A → (∀ i, α i ∈ Set.Icc a A) →
      0 < δ → δ < 1 / 2 → 0 < r → r < 1 / 6 →
      ∀ (Est : Kernel (Fin n → E d) (Param k d)), IsMarkovKernel Est →
      ∀ (Ev : Set ((Param k d × (Fin n → Fin k) × (Fin n → E d)) × Param k d)),
        ((joint k d n σ α) ⊗ₘ (Est.comap (fun p => p.2.2) measurable_snd.snd)) Evᶜ ≤
          ENNReal.ofReal (δ ^ 2 / 6) →
        (∀ q ∈ Ev, q.2 ∈ Theta k d ∧ OrbitClose q.2 q.1.1 r ∧ OrbitDisjoint q.2 (3 * r)) →
      ∀ (Alg : Kernel ((Fin n → E d) × Param k d) (Param k d × Equiv.Perm (Fin k))),
        IsMarkovKernel Alg →
        (∀ q ∈ Ev, Alg (q.1.2.2, q.2) (ballB q.2 (3 * r) ×ˢ Set.univ)ᶜ = 0 ∧
          tv (Alg (q.1.2.2, q.2)) (lifted σ α q.1.2.2 q.2 (3 * r)) ≤ δ / 2) →
      (∀ (x : Fin n → E d) (θ : Param k d) (c : Equiv.Perm (Fin k)), θ ∈ Theta k d →
          Machine.HaltsWithin Q
            ([(k : ℝ), (d : ℝ), (n : ℝ), σ] ++ List.ofFn α ++ Machine.dataCells x ++
              Machine.paramCells θ ++ List.ofFn (fun i => ((c i : ℕ) : ℝ) + 1))
            (C * n * d * k + C)) ∧
      xLaw k d n σ α {x | δ < Machine.tvLabels (fun o =>
          (((Est x ⊗ₘ Alg.comap (fun θbar => (x, θbar)) measurable_prodMk_left).prod
              Machine.tapeLaw) {p |
            (Machine.finalState Q Machine.noOracle
              ([(k : ℝ), (d : ℝ), (n : ℝ), σ] ++ List.ofFn α ++ Machine.dataCells x ++
                Machine.paramCells p.1.2.1 ++
                List.ofFn (fun i => ((p.1.2.2 i : ℕ) : ℝ) + 1)) p.2).bind
              (Machine.decodeLabels k n) = o}).toReal)
          (labelPost σ α x)} ≤ ENNReal.ofReal δ := by sorry

end GMMPostSamp.Main
