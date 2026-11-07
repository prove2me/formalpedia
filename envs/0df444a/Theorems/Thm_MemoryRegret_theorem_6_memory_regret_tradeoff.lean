-- Prove2me | Theorems.Thm_MemoryRegret_theorem_6_memory_regret_tradeoff
-- name    : MemoryRegret.theorem_6_memory_regret_tradeoff
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:40:42.346246+00:00
-- url     : https://prove2.me/theorems/93b2d829-f77e-4f19-95eb-204a20a17363
-- title:
--   Theorem 6 — low regret requires memory polynomial in the SQ dimension
-- statement:
--   There are universal constants $C>0$, $c_1>0$, $K$ and $D_0$ with the following property. Let $X$ be a finite set and $H\subseteq\{0,1\}^X$ a hypothesis class with $d=\mathrm{SQDim}(H)\ge D_0$, let $T\ge K(\log_2d)^4$, and let $L$ be a (randomized) online learner with state space $\sigma$ which, against every obliviously chosen sequence of $T$ labeled examples, has regret at most $R_T$ with respect to $H$ with probability at least $0.9$. Then
--   $$\log_2|\sigma|\ge c_1\min\{T^{1/4},d^C\}\qquad\text{or}\qquad R_T\ge\min\{T^{3/4},d^C\sqrt T\}.$$
--
--   That is, an online learner either uses memory polynomial in the statistical query dimension (or in $T^{1/4}$) or has regret far above the information-theoretic rate.
--
--   Differences from the source:
--   - reading: "there exists constant C > 0", printed after A is introduced → C universal, quantified first; reason: the informal main theorem (p.4) says "universal constant" and the proof takes C = c/4 = α/40; the literal order would be the weaker reading
--   - encoding: d larger than a sufficiently large constant, T = ω(log⁴ d), Ω(min{T^{1/4}, d^C}) bits → ∃ D₀, K, c₁: d ≥ D₀, T ≥ K·(log₂ d)⁴, log₂|σ| ≥ c₁·min{T^{1/4}, d^C}; reason: the standard meaning; the ∃K form implies the ω form, and the proof uses ω(log⁴ d) only through ε < 1/(10³r) and ε²m ≤ 1/(10⁶r²)
--   - generalization: an online algorithm A with memory in bits → any Learner: a finite state set σ with memory log₂|σ|, a random seed drawn once from a finite seed law (not counted as memory), and deterministic prediction and update rules that may depend on the seed and the round; reason: this contains every S-bit randomized online learner, with |σ| ≤ 2^S, whether its random bits are fresh per round or fixed in advance; the proof (Theorem 11 into a randomized branching program, then Theorem 4, which fixes the randomness, p.12) covers it
--   - encoding: H ⊆ {0,1}^X, regret eq. (1) at most R_T → H a Set (X → Bool), labels Bool, the event ∀ h ∈ H, M ≤ M_h + R; reason: for nonempty H, which d ≥ D₀ ≥ 1 forces, this is eq. (1) at most R
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), Theorem 6, p.30

import Mathlib
import Definitions.Def_MemoryRegret_sqDim
import Definitions.Def_MemoryRegret_Learner

namespace MemoryRegret

/-- **Theorem 6 (memory–regret tradeoff from SQ dimension).**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
Theorem 6, p.30.

There are universal constants `C > 0`, `c₁ > 0`, `K` and `D₀` such that the following holds.
Let `X` be a finite set and `H ⊆ {0,1}^X` a hypothesis class with `d = SQDim(H) ≥ D₀`, let
`T ≥ K·(log₂ d)⁴`, and let `L` be a (randomized) online learner with state space `σ` which,
against every obliviously chosen sequence `(x_1, y_1), …, (x_T, y_T)`, has regret at most `R_T`
with respect to `H` with probability at least `0.9`. Then `L` uses at least
`c₁·min{T^{1/4}, d^C}` bits of memory (`log₂|σ| ≥ c₁·min{T^{1/4}, d^C}`), or
`R_T ≥ min{T^{3/4}, d^C √T}`.

**Formalization Note.** `C` is universal and quantified first (the proof takes `C = c/4` with
`c = α/10` and `α` from Lemma 4.1; the informal main theorem, p.4, says "There exists a
universal constant"). "d larger than a sufficiently large constant", "T = ω(log⁴ d)" and
"Ω(min{T^{1/4}, d^C}) bits" are `d ≥ D₀`, `T ≥ K·(log₂ d)⁴` and `c₁·min{…} ≤ log₂|σ|`; the
regret threshold `min{T^{3/4}, d^C√T}` and the probability `0.9` are exact. The learner model
is `Learner` (a seed law over deterministic finite-state learners with state type `σ`; this
contains learners that draw fresh random bits every round) and the guarantee is
`AchievesRegret` (for every sequence, with probability ≥ 0.9, mistakes ≤ those of every
`h ∈ H` plus `R_T`). -/
theorem theorem_6_memory_regret_tradeoff :
    ∃ C : ℝ, 0 < C ∧ ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ K D₀ : ℝ,
      ∀ (X : Type) [Fintype X] (H : Set (X → Bool)),
        D₀ ≤ (sqDim H : ℝ) →
        ∀ T : ℕ, K * Real.logb 2 (sqDim H) ^ 4 ≤ T →
        ∀ (σ : Type) [Fintype σ] (Ω : Type) [Fintype Ω] (L : Learner X σ T Ω) (R : ℝ),
          AchievesRegret H L R (9 / 10) →
          c₁ * min ((T : ℝ) ^ (1 / 4 : ℝ)) ((sqDim H : ℝ) ^ C) ≤ Real.logb 2 (Fintype.card σ) ∨
          min ((T : ℝ) ^ (3 / 4 : ℝ)) ((sqDim H : ℝ) ^ C * Real.sqrt T) ≤ R := by sorry

end MemoryRegret
