-- Prove2me | Theorems.Thm_MemoryRegret_lemma_6_3_mistake_estimate
-- name    : MemoryRegret.lemma_6_3_mistake_estimate
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:06.866395+00:00
-- url     : https://prove2.me/theorems/b9a86a1f-6e5a-4bea-b111-6c034883c200
-- title:
--   Lemma 6.3 — estimating the mistake count with $O(\log T_{\mathrm{block}})$ extra bits
-- statement:
--   There is an absolute constant $K$ such that for all $m,T_{\mathrm{block}}$ with $T=mT_{\mathrm{block}}$ and all $\epsilon\le\frac12$ with $\epsilon\sqrt T>18$ there is a counter: a finite automaton with at most $K(T_{\mathrm{block}}+1)^K$ states (that is, $O(\log T_{\mathrm{block}})$ bits), read once per block with the number $M_j$ of mistakes in block $j$, together with an output function. For every distribution $\mu$ on a finite set, every finite class and every (possibly randomized) online algorithm run on the flattened stream, with probability at least $0.99$ the output is within $\epsilon T/40$ of the total $M=\sum_jM_j$, both under the NO distribution $\mathcal D_0$ and under the YES distribution $\mathcal D_1$.
--
--   This lets a low-memory distinguisher simulate an online learner and threshold its number of mistakes.
--
--   Differences from the source:
--   - reading: the mistake count can be estimated within ϵT/40 using O(log T_block) additional bits of memory → a counter automaton fed the block mistake counts, with at most K(T_block + 1)^K states, chosen before µ, the class and the algorithm; reason: the source proof constructs exactly such a counter (C ← C + round((M_j − m/2)/a), with an exceptional state); this is the stronger reading
--   - encoding: Ber(·, ½ + ϵ) with ϵ unrestricted above → ϵ ≤ ½; reason: this excludes only undefined cases; ϵ > 0 follows from ϵ√T > 18
--   - generalization: the learner of Theorem 11 → any finite-seed randomized online algorithm, with no memory bound; reason: the proof uses no memory bound on the learner, and a memory-bounded learner is such an algorithm
--   - generalization: the class H ⊆ {0,1}^X with h uniform on H → an indexed family hyp : ι → X → Bool with i uniform on ι; reason: ι = H with hyp h = h is the source statement; the family form also covers the [d]-indexed matrix of Lemma 4.1 and allows repetitions
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), Lemma 6.3, p.37

import Mathlib
import Definitions.Def_MemoryRegret_IsProbVec
import Definitions.Def_MemoryRegret_streamD1
import Definitions.Def_MemoryRegret_RandOnlineAlg

namespace MemoryRegret

/-- **Lemma 6.3 (estimating the mistake count with `O(log T_block)` extra bits).**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
Lemma 6.3, p.37.

There is an absolute constant `K` such that: for all `m, T_block` with `T = m·T_block` and all
`ϵ ≤ ½` with `ϵ√T > 18`, there is a counter, a finite automaton with at most
`K·(T_block + 1)^K` states (so `O(log T_block)` bits), an initial state `q₀`, a transition `upd`
read once per block with that block's mistake count `M_j`, and an output `est`, such that for
every distribution `µ` on a finite `X`, every finite class `(hyp i)_{i∈ι}` and every
(possibly randomized) online algorithm run on the flattened stream, the output is within `ϵT/40`
of the total number of mistakes `M = ∑_j M_j` with probability at least `0.99`, both under the
NO distribution `𝒟_0` and under the YES distribution `𝒟_1` (Definition 3).

**Formalization Note.** "Estimated … using O(log T_block) additional bits of memory" is read as
a counter automaton fed the per-block mistake counts, chosen before `µ`, the class and the
algorithm (the proof's counter `C ← C + round((M_j − m/2)/a)` with `a = ϵm/20` and an
exceptional state is of this form). `ϵ ≤ ½` is added so that `Ber(·, ½ + ϵ)` is a distribution.
The YES case uses `h` uniform on `ι`. -/
theorem lemma_6_3_mistake_estimate :
    ∃ K : ℕ, ∀ (m Tb : ℕ) (ϵ : ℝ), ϵ ≤ 1 / 2 → 18 < ϵ * Real.sqrt ((m * Tb : ℕ) : ℝ) →
      ∃ (Q : Type) (_ : Fintype Q), (Fintype.card Q : ℝ) ≤ K * ((Tb : ℝ) + 1) ^ K ∧
        ∃ (q₀ : Q) (upd : Q → ℕ → Q) (est : Q → ℝ),
          ∀ (X : Type) [Fintype X] (μ : X → ℝ), IsProbVec μ →
          ∀ (ι : Type) [Fintype ι] [Nonempty ι] (hyp : ι → X → Bool)
            (Ω : Type) [Fintype Ω] (A : RandOnlineAlg X (m * Tb) Ω),
            (99 / 100 : ℝ) ≤ ∑ s : Fin Tb → X × (Fin m → Bool), streamD0 μ ϵ s *
              wprob A.seedLaw (fun ω =>
                |est ((List.finRange Tb).foldl (fun q j => upd q (blockMistakes A ω s j)) q₀) -
                  A.algMistakes ω (flattenStream s)| ≤ ϵ * ((m * Tb : ℕ) : ℝ) / 40) ∧
            (99 / 100 : ℝ) ≤ ∑ s : Fin Tb → X × (Fin m → Bool), streamD1 μ hyp ϵ s *
              wprob A.seedLaw (fun ω =>
                |est ((List.finRange Tb).foldl (fun q j => upd q (blockMistakes A ω s j)) q₀) -
                  A.algMistakes ω (flattenStream s)| ≤ ϵ * ((m * Tb : ℕ) : ℝ) / 40) := by sorry

end MemoryRegret
