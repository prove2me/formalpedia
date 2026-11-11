-- Prove2me | Theorems.Thm_LogitRankDistill_lemma_5_2
-- name    : LogitRankDistill.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:58:40.307889+00:00
-- url     : https://prove2.me/theorems/0880c421-1978-4095-99b2-57dde5d5b260
-- title:
--   Lemma 5.2 — a barycentric spanner of O((N/η)² log(N/(ηδ))) samples is a distributional spanner with probability 1 − δ
-- statement:
--   There is a constant $C>0$ such that for every distribution $P$ on $\mathbb R^N$ and all $\eta,\delta,\beta>0$, if
--   $$m\ge C\,(N/\eta)^2\log\big(N/(\eta\delta)\big),$$
--   then with probability at least $1-\delta$ over i.i.d. $u_1,\dots,u_m\sim P$, every $\beta$-barycentric spanner $u_{i_1},\dots,u_{i_N}$ of $\{u_1,\dots,u_m\}$ is an $(\eta,\beta)$-distributional spanner for $P$ (Definition 5.3).
--   It is the reason DistSpanner (Algorithm 3) succeeds, and with a union bound it gives Lemma 5.4.
--
--   **Formalization Note.** $P$ is a probability measure on `Fin N → ℝ`; the samples have law `Measure.pi`. The statement bounds by $\delta$ the outer probability of the set of sample tuples admitting a $\beta$-barycentric spanner (indices $i_1,\dots,i_N$, repetitions allowed) that is not an $(\eta,\beta)$-distributional spanner.
--
--   Differences from the source:
--   - encoding: P ∈ Δ(R^N) a distribution over vectors L ∈ S ⊂ R^N → P any probability measure on Fin N → ℝ (S = R^N); reason: S plays no role in the statement; same instances
--   - encoding: with probability at least 1 − δ, any β-barycentric spanner is distributional → outer measure of the samples admitting a bad spanner ≤ δ; reason: equivalent, and avoids a measurability side condition
--   - reading: m ≥ Ω((N/η)² log(N/(ηδ))) → ∃ C > 0 universal, m ≥ C (N/η)² log(N/(ηδ)); reason: Ω(·) is an absolute constant
-- source:
--   Golowich, Liu, Shetty, Provably Distilling from Modern Language Models via Low Logit Rank, manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), p. 23, Lemma 5.2

import Mathlib
import Definitions.Def_LogitRankDistill_Spanners

open MeasureTheory

namespace LogitRankDistill

/-- **Lemma 5.2** (p. 23, from [LM25]): there is a constant `C > 0` such that for every
distribution `P` on `ℝ^N` and all `η, δ, β > 0`, if `m ≥ C (N/η)² log(N/(ηδ))` then, with
probability at least `1 − δ` over i.i.d. `u_1, …, u_m ∼ P`, every `β`-barycentric spanner
`u_{i_1}, …, u_{i_N}` of `{u_1, …, u_m}` is an `(η, β)`-distributional spanner for `P`. Stated as:
the (outer) probability of the samples admitting a `β`-barycentric spanner that is not an
`(η, β)`-distributional spanner is at most `δ`. Spanner indices may repeat. -/
theorem lemma_5_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (P : Measure (Fin N → ℝ)) [IsProbabilityMeasure P]
      (η δ β : ℝ), 0 < η → 0 < δ → 0 < β → ∀ m : ℕ,
        C * ((N : ℝ) / η) ^ 2 * Real.log ((N : ℝ) / (η * δ)) ≤ m →
        Measure.pi (fun _ : Fin m => P)
          {u : Fin m → Fin N → ℝ | ∃ ι : Fin N → Fin m,
            IsBarySpanner β (fun i => u (ι i)) (Set.range u) ∧
            ¬ IsDistSpanner P id (fun i => u (ι i)) η β} ≤ ENNReal.ofReal δ := by sorry

end LogitRankDistill
