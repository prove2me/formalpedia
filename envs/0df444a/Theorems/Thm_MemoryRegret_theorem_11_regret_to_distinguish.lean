-- Prove2me | Theorems.Thm_MemoryRegret_theorem_11_regret_to_distinguish
-- name    : MemoryRegret.theorem_11_regret_to_distinguish
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:40:23.101946+00:00
-- url     : https://prove2.me/theorems/d09b151f-e317-4522-9cf2-15aa8350a41b
-- title:
--   Theorem 11 — low regret implies distinguishing
-- statement:
--   There is an absolute constant $K$ such that the following holds. Let $\mu$ be a distribution on a finite set $X$, $H$ a finite nonempty class, $T=mT_{\mathrm{block}}$, and let $L$ be an online learner with state space $\sigma$ that, against every obliviously chosen sequence of length $T$, has regret at most $R_T$ with respect to $H$ with probability at least $1-\delta$, where $\delta\le1/10$. Then for all $\epsilon>\max\{4R_T/T,\,18/\sqrt T\}$ with $m\le1/(160^2\epsilon^2)$, there is a randomized branching program of length $T_{\mathrm{block}}$ over the alphabet $X\times\{0,1\}^m$, of width at most $K\,|\sigma|\,(T_{\mathrm{block}}+1)^K$, which answers NO with probability at least $4/5$ under $\mathcal D_0$ and YES with probability at least $4/5$ under $\mathcal D_1$.
--
--   This is the reduction from the distinguishing problem to online learning: a low-regret learner with little memory would give a distinguisher with little memory.
--
--   **Formalization Note** The width bound is the learner's memory plus $O(\log T_{\mathrm{block}})$ bits. The program's randomness is the seed (the learner's random choices) and is not counted in the width, as in §3.2, p.12. The conditions on $\epsilon$ force $T\ge1$, $m\ge1$ and $\epsilon\le1/160$.
--
--   Differences from the source:
--   - reading: algorithm A can be used to distinguish … while using O(log T_block) extra bits of memory → there is a randomized branching program of width at most K·|σ|·(T_block + 1)^K, with K absolute, succeeding with probability at least 4/5 on each side; reason: this is the object that the source proof builds and that Theorem 4 takes as input
--   - generalization: an online learner A → any Learner: a finite state set σ, a random seed drawn once from a finite seed law, and deterministic prediction and update rules that may depend on the seed and the round; reason: this contains every randomized online learner with |σ| states, whether its random bits are fresh per round or fixed in advance; the proof turns the learner's randomness into the distinguisher's seed
--   - generalization: the class H ⊆ {0,1}^X with h uniform on H → an indexed family hyp : ι → X → Bool with i uniform on ι; reason: ι = H with hyp h = h is the source statement; the family form also covers the [d]-indexed matrix of Lemma 4.1 and allows repetitions
--   - encoding: ϵ > max{4R_T/T, 18/√T}, m ≤ 1/(160²ϵ²) → 4R < ϵT, 18 < ϵ√T, m·160²ϵ² ≤ 1; reason: multiplicative form avoids x/0 = 0; the two forms agree because the conditions force T ≥ 1 and ϵ > 0
--   - encoding: regret at most R_T as in eq. (1) → mistakes ≤ those of every h ∈ range hyp plus R; reason: for a nonempty class this is the minimum over h
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), Theorem 11, p.33

import Mathlib
import Definitions.Def_MemoryRegret_IsProbVec
import Definitions.Def_MemoryRegret_streamD1
import Definitions.Def_MemoryRegret_BranchingProgram
import Definitions.Def_MemoryRegret_Learner

namespace MemoryRegret

/-- **Theorem 11 (low regret implies distinguishing).**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
Theorem 11, p.33.

There is an absolute constant `K` such that: let `µ` be a distribution on a finite set `X`,
`(hyp i)_{i∈ι}` a finite nonempty class `H`, `T = m·T_block`, and `L` an online learner with
state space `σ` that, against every obliviously chosen length-`T` sequence, has regret at most
`R_T` with respect to `H` with probability at least `1 − δ`, `δ ≤ 1/10`. Then for every `ϵ`
with `ϵ > max{4R_T/T, 18/√T}` and `m ≤ 1/(160²ϵ²)` there is a randomized branching program of
length `T_block` over the alphabet `X × {0,1}^m` with at most `K·|σ|·(T_block+1)^K` states per
layer (the learner's memory plus `O(log T_block)` bits) that answers NO with probability at
least `4/5` under `𝒟_0` and YES with probability at least `4/5` under `𝒟_1`.

**Formalization Note.** "A can be used to distinguish … while using O(log T_block) extra bits"
is read as the existence of such a program whose width is `|σ|` times a polynomial in
`T_block` with an absolute constant. The program's randomness is a seed (the learner's random
choices); it is not counted in the width, as in §3.2 ("Without loss of generality, we can
assume B is deterministic"). `𝒟_1` draws `h` uniformly from the index type `ι`, and the regret
is against `Set.range hyp`. The conditions on `ϵ` are written multiplicatively; they force
`T ≥ 1`, `m ≥ 1` and `ϵ ≤ 1/160`. -/
theorem theorem_11_regret_to_distinguish :
    ∃ K : ℕ, ∀ (X : Type) [Fintype X] (μ : X → ℝ), IsProbVec μ →
      ∀ (ι : Type) [Fintype ι] [Nonempty ι] (hyp : ι → X → Bool)
        (σ : Type) [Fintype σ] (Ω₀ : Type) [Fintype Ω₀] (m Tb : ℕ) (L : Learner X σ (m * Tb) Ω₀)
        (R δ : ℝ),
        δ ≤ 1 / 10 → AchievesRegret (Set.range hyp) L R (1 - δ) →
        ∀ ϵ : ℝ, 4 * R < ϵ * ((m * Tb : ℕ) : ℝ) → 18 < ϵ * Real.sqrt ((m * Tb : ℕ) : ℝ) →
          (m : ℝ) * (160 ^ 2 * ϵ ^ 2) ≤ 1 →
          ∃ (S Ω : Type) (_ : Fintype S) (_ : Fintype Ω)
            (P : RandBP S (X × (Fin m → Bool)) Tb Ω),
            (Fintype.card S : ℝ) ≤ K * Fintype.card σ * ((Tb : ℝ) + 1) ^ K ∧
            4 / 5 ≤ P.outProb (streamD0 μ ϵ) false ∧
            4 / 5 ≤ P.outProb (streamD1 μ hyp ϵ) true := by sorry

end MemoryRegret
