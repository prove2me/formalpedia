-- Prove2me | Theorems.Thm_GMMPostSamp_Main_corollary_1
-- name    : GMMPostSamp.Main.corollary_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:28:42.718014+00:00
-- url     : https://prove2.me/theorems/2eed1d23-cac0-4c08-bcc2-97860c3d3596
-- title:
--   Corollary 1 — on E, Algorithm 1 with δ/(8T)-oracles for T = ⌈2 log(8D/δ²)⌉ steps is within δ/2 of the lifted posterior
-- statement:
--   There are an admissible LearnGMM program and a universal $C>0$ such that for all $k,d,n\ge1$, $\sigma>0$, $0<a\le A$, $\alpha\in[a,A]^k$ and $\delta\in(0,\frac16)$, with the notation of Lemma 7 at $\delta'=\delta^2/24$ ($\tau$, $K$, $r$ and the hypotheses on $d,n$), $D=Ak\log\frac2\tau$, $T=\lceil2\log\frac{8D}{\delta^2}\rceil$ and
--   $$n\ge\frac{12800(1+\sigma^2)^3A^2k}{\tau^4},$$
--   outside the event $E$ of Proposition 4 at $\delta'$ (probability at most $\delta'$ over Model 1 and the tapes), for all $\frac\delta{8T}$-conditional sampling oracles $(O_\theta,O_c)$ for $\tilde\Pi_B$, Algorithm 1 run for $T$ iterations with these oracles in lines 4 and 5 outputs $(\theta,c)$ with
--   $$\mathrm{TV}\big(\mathrm{Law}(\theta,c),\tilde\Pi_B\big)\le\frac\delta2.$$
--   This is the mixing guarantee of the lifted Gibbs sampler.
--
--   **Formalization Note.** Oracles are Markov kernels; $T$ is a natural number (ceiling).
--
--   Differences from the source:
--   - reading: following the notation of Lemma 7 (with δ ← δ²/24); under the event E from Proposition 4 (with δ ← δ²/24) → Lemma 7's and Proposition 4's hypotheses at δ′ = δ²/24 with one universal C and one LearnGMM program (with Proposition 4's runtime); an event of probability ≥ 1 − δ′ on which Proposition 4's conclusions hold and the TV bound holds for every pair of oracles; reason: E is Proposition 4's (and Lemma 7's) event; the corollary is stated on it
--   - encoding: δ/(8T)-conditional sampling oracles in Lines 4 and 5 → any Markov kernels (Kθ, Kc) with IsCondOracles at level δ/(8T) (Definition 1, θ ∈ B with all w_i > 0); reason: oracles are randomized algorithms; (32) is defined for positive weights
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), p. 22, Corollary 1

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_PolyVoting_dirichletMeasure
import Definitions.Def_GMMPostSamp_Main_Toolkit
import Definitions.Def_GMMPostSamp_Main_Model
import Definitions.Def_GMMPostSamp_Main_Machine

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-- Corollary 1 (p. 22): with the notation of Lemma 7 at `δ' = δ²/24`, `T = ⌈2 log(8D/δ²)⌉`,
`D = Ak log(2/τ)` and `n ≥ 12800(1 + σ²)³A²k/τ⁴`: outside the event `E` of Proposition 4 at
`δ'` (probability at most `δ'` over Model 1 and LearnGMM's tapes), Algorithm 1 run for `T`
iterations with any `δ/(8T)`-conditional sampling oracles in lines 4 and 5 outputs `(θ, c)` with
`TV(Law((θ, c)), Π̃_B) ≤ δ/2`. -/
theorem corollary_1 : ∃ L : Machine.Program, Machine.Admissible L ∧ ∃ C : ℝ, 0 < C ∧
    ∀ k d n : ℕ, 1 ≤ k → 1 ≤ d → 1 ≤ n → ∀ (σ a A δ r : ℝ) (α : Fin k → ℝ),
      0 < σ → 0 < a → a ≤ A → (∀ i, α i ∈ Set.Icc a A) → 0 < δ → δ < 1 / 6 →
      let τ : ℝ := (1 / (A * k)) * ((δ ^ 2 / 24) / (8 * k)) ^ (1 / a)
      let K : ℝ := C * (1 / τ ^ 3 + 1 / σ ^ 6)
      0 < r → r ≤ τ ^ 2 / (C * K * (1 + σ ^ 6)) → r < 1 / 6 →
      C * ((k : ℝ) + Real.log (1 / (δ ^ 2 / 24))) ≤ d →
      C * (1 + σ ^ 12) / τ ^ 4 * (1 / τ ^ 2 + d / σ ^ 2) ^ 2 * Real.log (d / (δ ^ 2 / 24)) +
          C * (d : ℝ) ^ ((3 : ℝ) / 2) ≤ n →
      C * ((d : ℝ) ^ 3 * (k : ℝ) ^ 11 * (1 + σ ^ 8) / (τ ^ 6 * r ^ 2)) ≤ n →
      let D : ℝ := A * k * Real.log (2 / τ)
      let T : ℕ := ⌈2 * Real.log (8 * D / δ ^ 2)⌉₊
      12800 * (1 + σ ^ 2) ^ 3 * A ^ 2 * k / τ ^ 4 ≤ n →
      (∀ x : Fin n → E d, Machine.HaltsWithin L
          ([(k : ℝ), (d : ℝ), (n : ℝ), (δ ^ 2 / 24)] ++ Machine.dataCells x)
          (C * (n * (d : ℝ) ^ 2 + n * (k : ℝ) ^ 3) + C)) ∧
      ((joint k d n σ α).prod Machine.tapeLaw) {q | ¬ ∃ θbar : Param k d,
          (Machine.finalState L Machine.noOracle
              ([(k : ℝ), (d : ℝ), (n : ℝ), (δ ^ 2 / 24)] ++ Machine.dataCells q.1.2.2) q.2).map
              (Machine.decodeParam k d) = some θbar ∧
            θbar ∈ Theta k d ∧ OrbitClose θbar q.1.1 r ∧ OrbitDisjoint θbar (3 * r) ∧
            ∀ (Kθ : Kernel (Param k d) (Equiv.Perm (Fin k)))
              (Kc : Kernel (Equiv.Perm (Fin k)) (Param k d)),
              IsMarkovKernel Kθ → IsMarkovKernel Kc →
              IsCondOracles σ α q.1.2.2 θbar (3 * r) (δ / (8 * T)) Kθ Kc →
              tv (alg1Law Kc Kθ θbar T) (lifted σ α q.1.2.2 θbar (3 * r)) ≤ δ / 2}
        ≤ ENNReal.ofReal (δ ^ 2 / 24) := by sorry

end GMMPostSamp.Main
