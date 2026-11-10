-- Prove2me | Theorems.Thm_MulticlassOmni_Lipschitz_lemma_B_4
-- name    : MulticlassOmni.Lipschitz.lemma_B_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:14:40.997933+00:00
-- url     : https://prove2.me/theorems/0d82b0c5-d41b-4728-964e-c6bc5243023e
-- title:
--   Lemma B.4 — in both the §4.1 and the §5.1 construction, few samples force $\ge N/4$ Hamming errors with probability $\ge9/10$
-- statement:
--   There are absolute constants $c_0,c_{\mathrm{stat}}>0$ such that, with $\theta^\star$ uniform on $X\to\{0,1\}$, $S\sim D_{\theta^\star}^n$ and $D_\theta$ the distribution with uniform marginal on $X$ and conditional label law $q_{\theta(x)}(x)$:
--   1. **Lipschitz proper-loss setting (§4.1).** For the packing constant $C_{\mathrm{pack}}>0$ there is $\eta_0>0$ such that for every integer $k\ge3$, every $0<\eta\le\eta_0$ and every Section 4.1 domain $x_1,\dots,x_N$ with the vectors $q_b(x)$ of (23): $q_b(x)\in\Delta_k$ for every $x\in X$, $b\in\{0,1\}$; and if $n\le c_0N/(k\eta^2)$, every possibly randomized estimator $\hat\theta:X\to\{0,1\}$ based on $S$ satisfies $\Pr_{\theta^\star,S,\hat\theta}\big[|\{x:\hat\theta(x)\ne\theta^\star(x)\}|\ge N/4\big]\ge\tfrac9{10}$.
--   2. **GLM setting (§5.1).** For every integer $k\ge3$, every $0<\varepsilon\le1/512$ and every domain $x_1,\dots,x_N$ as in §5.1 (zero-sum packing at scale $\varepsilon$, $N$ a multiple of four, $N\ge512$) with $q_b(x)=\bar v+\tfrac{4R_b}{k}x$, $R_b=\tfrac1{32}+48\varepsilon b$ (64): $q_b(x)\in\Delta_k$ for every $x$, $b$; and if $n\le c_{\mathrm{stat}}N/\varepsilon^2$, the same probability bound $\ge9/10$ holds.
--
--   Differences from the source:
--   - generalization: absolute constants c0, c_stat for the construction built on Lemma B.2's packing constant, with η ≤ η0 for the η0 of Lemma B.3 → ∃ c0, c_stat > 0 first, then ∀ C_pack > 0, ∃ η0 > 0 (η0 may depend on C_pack, c0 may not), for every truncation of every set satisfying Lemma B.2's conclusion with that C_pack; reason: instantiating C_pack with Lemma B.2's constant gives the source's first setting; Lemma B.3's η0 is itself only asserted to exist
--   - generalization: the §5.1 domain: the packing from Lemma B.1 (for sufficiently small ε), with N a multiple of four and N ≥ 512 → any injective x : Fin N → ℝ^k whose range has Lemma B.1's geometric properties at scale ε, with 4 ∣ N and N ≥ 512, for every ε ∈ (0, 1/512]; Lemma B.1's cardinality lower bound and its ε ≤ ε0 are not assumed; reason: every source domain satisfies these hypotheses
--   - encoding: a possibly randomized estimator θ̂ based on S (with independent private randomness) and the probability over θ*, S, θ̂ → a conditional law est S on the finite set Fin N → Fin 2 for each S (IsRandEstimator) and the explicit finite sum hammingFailProb; reason: only the conditional law of θ̂ given S enters the probability, and it can be any distribution on the finite output set
--   - encoding: the domain X = {x_1, …, x_N} and functions π, θ : X → {0, 1} → an injective enumeration x : Fin N → ℝ^k and π, θ : Fin N → Fin 2 (π i is π(x_{i+1})); reason: same objects, indexed
--   - encoding: labels [k] = {1, …, k} → Fin k, the source label y is the index y − 1 (label 1 is index 0); reason: relabeling; same instances
-- source:
--   Hu, Luo, Schneider, Yang (2026), Sample Complexity of Multiclass Omniprediction, supplied PDF (SHA-256 aaa73474…584f0, citation basis published; STOC 2027 submission), Lemma B.4, p. 58

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_Packings
import Definitions.Def_MulticlassOmni_Lipschitz_Construction
import Definitions.Def_MulticlassOmni_Lipschitz_StatLowerBound

namespace MulticlassOmni.Lipschitz

/-- **Lemma B.4 (Statistical lower bound for the two constructions)**, Hu, Luo, Schneider, Yang
(2026), p. 58. There are absolute constants `c₀, c_stat > 0` such that:
1. (Lipschitz proper-loss construction, §4.1) for the packing constant `Cpack > 0` of Lemma B.2
   there is `η₀ > 0` such that for every integer `k ≥ 3`, every `0 < η ≤ η₀` and the Section 4.1
   domain `x_1, …, x_N` with the vectors `q_b(x)` of (23): `q_b(x) ∈ Δ_k` for all `x, b`, and if
   `n ≤ c₀ N/(k η²)` then every randomized estimator `θ̂` based on `S` satisfies
   `Pr_{θ*, S, θ̂}[|{x : θ̂(x) ≠ θ*(x)}| ≥ N/4] ≥ 9/10`;
2. (GLM construction, §5.1) for every integer `k ≥ 3`, every `0 < ε ≤ 1/512` and every zero-sum
   packing `x_1, …, x_N` as in §5.1 (`N` a multiple of four, `N ≥ 512`) with the vectors `q_b(x)`
   of (64): `q_b(x) ∈ Δ_k` for all `x, b`, and if `n ≤ c_stat N/ε²` then the same bound holds.
Here `θ*` is uniform on `X → {0, 1}`, `S ∼ D_{θ*}^n`, and `D_θ` has uniform marginal on `X` and
conditional label distribution `q_{θ(x)}(x)`. -/
theorem lemma_B_4 :
    ∃ c₀ c_stat : ℝ, 0 < c₀ ∧ 0 < c_stat ∧
      (∀ Cpack : ℝ, 0 < Cpack → ∃ η₀ : ℝ, 0 < η₀ ∧
        ∀ k : ℕ, 3 ≤ k → ∀ η : ℝ, 0 < η → η ≤ η₀ →
          ∀ (N : ℕ) (x : Fin N → Fin k → ℝ), IsSection41Packing Cpack k η x →
            (∀ (b : Fin 2) (i : Fin N), qLip x η b i ∈ stdSimplex ℝ (Fin k)) ∧
            ∀ n : ℕ, (n : ℝ) ≤ c₀ * N / (k * η ^ 2) →
              ∀ est : (Fin n → Fin N × Fin k) → (Fin N → Fin 2) → ℝ, IsRandEstimator est →
                9 / 10 ≤ hammingFailProb (qLip x η) est) ∧
      (∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 512 →
        ∀ (N : ℕ) (x : Fin N → Fin k → ℝ), IsGLMPacking k ε x →
          (∀ (b : Fin 2) (i : Fin N), qGLM x ε b i ∈ stdSimplex ℝ (Fin k)) ∧
          ∀ n : ℕ, (n : ℝ) ≤ c_stat * N / ε ^ 2 →
            ∀ est : (Fin n → Fin N × Fin k) → (Fin N → Fin 2) → ℝ, IsRandEstimator est →
              9 / 10 ≤ hammingFailProb (qGLM x ε) est) := by sorry

end MulticlassOmni.Lipschitz
