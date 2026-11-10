-- Prove2me | Theorems.Thm_GoodHypotheses_Proper_theorem_3_4
-- name    : GoodHypotheses.Proper.theorem_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:15:12.826439+00:00
-- url     : https://prove2.me/theorems/aa36e164-a915-4db5-9571-c80e0a89625d
-- title:
--   Theorem 3.4 — MWU regret ≤ C(log n/(ηT) + ηB²) for losses in [a, b]
-- statement:
--   Run MWU with learning rate $\eta>0$ for $T$ rounds on $n$ items with losses $\ell^t_i\in[a,b]$, $a<b$, $B=b-a$. Then there is a constant $C>0$ such that for every item $i$
--   $$\frac1T\sum_{t=1}^T\big(\langle\tilde W^t,\ell^t\rangle-\ell^t_i\big)\le C\Big(\frac{\log n}{\eta T}+\eta B^2\Big).$$
--   The constant $C$ is universal: one $C$ serves every $n$, $T$, $\eta$, $a$, $b$ and loss sequence. This is the standard regret bound (Cesa-Bianchi–Lugosi, Theorem 2.2) used inside the stochastic MWU bound.
--
--   Differences from the source:
--
--   - reading: "there exists a constant C > 0" stated after a, b → ∃ C > 0 before n, T, η, a, b and the losses (one universal constant); reason: the stronger reading; it is how the paper uses the bound (Theorem 1.1 fixes T = cε⁻²log(n/δ) with one c)
--   - encoding: rounds t ∈ [T], W¹ = 1, W^{t+1} = W^t exp(−ηℓ^t) → 0-based rounds t < T with weight η ℓ 0 = 1 and the same update; reason: Lean convention; same weights
--   - encoding: losses may depend arbitrarily on the prior rounds' weights → an arbitrary loss sequence ℓ : ℕ → Fin n → ℝ; reason: the weights are a deterministic function of past losses, so every adaptive choice is one sequence
--   - encoding: items i ∈ [n] = {1, …, n} → i : Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, A Good Way to Find Good Hypotheses, STOC 2027 submission (manuscript sha256 a428fbe0…), p. 15, Theorem 3.4

import Mathlib
import Definitions.Def_GoodHypotheses_Proper_MWU

namespace GoodHypotheses.Proper

/-- Theorem 3.4 (MWU, p. 15), with "there exists a constant `C > 0`" read as one universal
constant: for all `n, T ≥ 1`, every learning rate `η > 0`, all reals `a < b` and every loss
sequence with `ℓ^t_i ∈ [a, b]` (rounds `0, …, T − 1`), every item `i` satisfies
`(1/T) ∑_t (⟨W̃^t, ℓ^t⟩ − ℓ^t_i) ≤ C (log n/(ηT) + η B²)` with `B = b − a`. -/
theorem theorem_3_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n T : ℕ) (η a b : ℝ) (ℓ : ℕ → Fin n → ℝ), 1 ≤ n → 1 ≤ T → 0 < η → a < b →
        (∀ t, t < T → ∀ i, a ≤ ℓ t i ∧ ℓ t i ≤ b) →
        ∀ i, (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (mixLoss η ℓ t - ℓ t i)
          ≤ C * (Real.log n / (η * T) + η * (b - a) ^ 2) := by sorry

end GoodHypotheses.Proper
