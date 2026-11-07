-- Prove2me | Theorems.Thm_NCPComm_claim_4_11
-- name    : NCPComm.claim_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:03:05.204215+00:00
-- url     : https://prove2.me/theorems/cc8c8205-4c96-4556-b8f8-910db82ee85b
-- title:
--   Claim 4.11 — laws of the light doubleton counts
-- statement:
--   The light doubleton counts are binomial,
--   $$
--   |\mathbf L^0_2|\equiv\mathrm{Bin}\Big(N-K,\tfrac12\big(\tfrac{s}{2(N-K)}\big)^2e^{-\frac{s}{2(N-K)}}\Big),\quad
--   |\mathbf L^1_2|\equiv\mathrm{Bin}\Big(\tfrac N3-K,\tfrac12\big(\tfrac{s}{2(N/3-K)}\big)^2e^{-\frac{s}{2(N/3-K)}}\Big),
--   $$
--   with mean difference
--   $$
--   \mathbb E[|\mathbf L^1_2|]-\mathbb E[|\mathbf L^0_2|]=\frac{s^2}4\Big(\frac{e^{-\frac{s}{2(N/3-K)}}}{2(N/3-K)}-\frac{e^{-\frac{s}{2(N-K)}}}{2(N-K)}\Big),
--   $$
--   and $\mathrm{Var}[|\mathbf L^1_2|]/\mathrm{Var}[|\mathbf L^0_2|]\le3.01$.
--
--   The mean difference is the size of the signal the reduction plants, and the variance ratio bounds how far the two normal approximations can be separated by their widths.
--
--   Differences from the source:
--   - encoding: D uniform on F_b(N, K) → π uniform on permutations, D = π(D_b); reason: the orbit map pushes the uniform law to the uniform law on the orbit; the page reads the randomness as "the heavy and light sets"
--   - encoding: the regime of §4: N ∈ 6ℕ → 3 ∣ N and 0 < K (with 3K < N eventually, from K = o(N)); reason: p.19 calls divisibility by 6 "only for convenience", and N ∈ 3ℕ is what Proposition 4.7 uses; N ∈ 6ℕ is a special case
--   - reading: the variance ratio, printed with no hypothesis → for all large n, under K, s = o(N); reason: the proof derives it "for all sufficiently large N"; printed with no hypothesis it fails for K close to N/3, so it inherits the regime of Claim 4.10
--   - generalization: "K = o(N) and s = o(N^{2/3})" (proof, p.26) → K, s = o(N); reason: the computation q₀, q₁ = o(1) and e^{s/(2n₀) − s/(2n₁)} → 1 uses only s = o(N); s = o(N^{2/3}) is a special case
--   - encoding: Var[|L¹₂|] / Var[|L⁰₂|] ≤ 3.01 → Var[|L¹₂|] ≤ 3.01·Var[|L⁰₂|]; reason: equivalent when the denominator is positive, and it avoids the Lean value x/0 = 0 at s = 0
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Claim 4.11, p.25; proof, p.26

import Mathlib
import Definitions.Def_NCPComm_idealSetup

open scoped NNReal ENNReal Topology
open Filter

namespace NCPComm

/-- **Claim 4.11, p.25** (Herman, The Communication Complexity of Verifying Distribution Properties,
STOC 2027 submission, manuscript sha256 714c0353…). The doubleton light counts are binomial,
`|L⁰₂| ≡ Bin(N-K, ½(s/(2(N-K)))² e^{-s/(2(N-K))})` and
`|L¹₂| ≡ Bin(N/3-K, ½(s/(2(N/3-K)))² e^{-s/(2(N/3-K))})`, their mean difference is the displayed
formula, and `Var[|L¹₂|]/Var[|L⁰₂|] ≤ 3.01`.

**Formalization Note** The two laws and the mean difference hold at every valid parameter. The page
states the variance ratio with no hypothesis; its proof derives it "for all sufficiently large `N`"
from `K = o(N)` and `s = o(N^{2/3})`. Here it is stated for all large `n` under `K, s = o(N)`, which
is all the computation uses. It is written `Var[|L¹₂|] ≤ 3.01·Var[|L⁰₂|]`, which avoids the Lean
value `x/0 = 0` at `s = 0`. -/
theorem claim_4_11 :
    (∀ (N K : ℕ) (s : ℝ≥0), ValidParams N K →
      let n₀ : ℝ := (N : ℝ) - K
      let n₁ : ℝ := (N : ℝ) / 3 - K
      (∀ k, ((idealSetup false N K s).map fun o => lightCount o 2) k =
        binomialMass (N - K)
          (1 / 2 * ((s : ℝ) / (2 * n₀)) ^ 2 * Real.exp (-((s : ℝ) / (2 * n₀)))) k) ∧
      (∀ k, ((idealSetup true N K s).map fun o => lightCount o 2) k =
        binomialMass (N / 3 - K)
          (1 / 2 * ((s : ℝ) / (2 * n₁)) ^ 2 * Real.exp (-((s : ℝ) / (2 * n₁)))) k) ∧
      pmfMean ((idealSetup true N K s).map fun o => lightCount o 2)
          - pmfMean ((idealSetup false N K s).map fun o => lightCount o 2)
        = (s : ℝ) ^ 2 / 4 * (Real.exp (-((s : ℝ) / (2 * n₁))) / (2 * n₁)
            - Real.exp (-((s : ℝ) / (2 * n₀))) / (2 * n₀))) ∧
    (∀ (N K : ℕ → ℕ) (s : ℕ → ℝ≥0),
      (∀ᶠ n in atTop, 3 ∣ N n ∧ 0 < K n) →
      Tendsto (fun n => (K n : ℝ) / N n) atTop (𝓝 0) →
      Tendsto (fun n => (s n : ℝ) / N n) atTop (𝓝 0) →
      ∀ᶠ n in atTop,
        pmfVar ((idealSetup true (N n) (K n) (s n)).map fun o => lightCount o 2)
          ≤ 3.01 * pmfVar ((idealSetup false (N n) (K n) (s n)).map fun o => lightCount o 2)) := by sorry

end NCPComm
