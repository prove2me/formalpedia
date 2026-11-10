-- Prove2me | Theorems.Thm_MinSumRadiiPTAS_Main_lemma_5_3
-- name    : MinSumRadiiPTAS.Main.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:02:03.958691+00:00
-- url     : https://prove2.me/theorems/f760da54-0ab7-47ad-97ae-0e4be1750524
-- title:
--   Lemma 5.3 — FormGroups keeps a clique together with probability $\ge 1 - (\log m + 1)/U$
-- statement:
--   **Lemma 5.3** (p. 17; proof p. 36). Let $H$ be a finite simple graph, $U \ge 1$ an integer, $C$ a clique of $H$ and $m$ the number of vertices $u$ with $d_H(u, C) \le 2U$. Run FormGroups with $D$ uniform on $\{U+1, \dots, 2U\}$ and an independent uniformly random permutation of $V(H)$. With probability at least
--   $$1 - \frac{\log m + 1}{U}$$
--   (natural logarithm) all vertices of $C$ end up in the same group.
--
--   Differences from the source:
--   - generalization: U = 2^{3L} (§5.1) → any integer U ≥ 1; reason: the proof uses nothing about U; specializes to U = 2^{3L}
--   - encoding: a uniformly random permutation (v_1, …, v_m) of V(H) and "probability" → a uniformly random bijection π : V ≃ Fin |V| (π v is the position of v), and the probability as the fraction of pairs (D, π) in {U+1, …, 2U} × (V ≃ Fin |V|); reason: same law; the leader of v is the first vertex of the permutation within graph distance D (Algorithm 6)
--   - encoding: graph distance d_H and d_H(u, C) → SimpleGraph.edist in ℕ∞ (∞ across components) and its infimum over C; reason: same distances
--   - generalization: the logarithmic bound is defined for m ≥ 1 (in particular every nonempty clique) → also permits C = ∅, with graphDistToSet = ∞ and Real.log 0 = 0; reason: a nonempty clique has m ≥ 1 and exactly the printed bound; for the empty clique the same-group event has probability 1 and the extended bound is 1 − 1/U ≤ 1
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, §5.1, Lemma 5.3, p. 17 (proof Appendix A, p. 36)

import Mathlib
import Definitions.Def_MinSumRadiiPTAS_Main_Partition

open scoped Classical

namespace MinSumRadiiPTAS.Main

/-- **Lemma 5.3** (p. 17; proof p. 36): let `C` be a clique of a finite simple graph `H` and `m` the
number of vertices `u` with `d_H(u, C) ≤ 2U`. With `D` uniform on `{U+1, …, 2U}` and an independent
uniformly random permutation of `V(H)`, FormGroups puts all vertices of `C` in the same group with
probability at least `1 − (log m + 1)/U` (natural logarithm). -/
theorem lemma_5_3 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (U : ℕ)
    (hU : 1 ≤ U) (C : Finset V) (hC : H.IsClique (C : Set V)) :
    let m : ℕ := (Finset.univ.filter (fun u => graphDistToSet H u C ≤ ((2 * U : ℕ) : ℕ∞))).card
    1 - (Real.log (m : ℝ) + 1) / (U : ℝ) ≤ fgSameGroupProb H U C := by sorry

end MinSumRadiiPTAS.Main
