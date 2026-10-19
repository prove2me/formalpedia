-- Prove2me | Theorems.Thm_OAI_LinearListHadwiger_Sampling_source_thinning_failure_structure
-- name    : OAI.LinearListHadwiger.Sampling.source_thinning_failure_structure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:46:35.069641+00:00
-- url     : https://prove2.me/theorems/17e7ae8c-e1d3-4d41-8c7d-7d1cfcebaf16
-- title:
--   Structure when random thinning of stable sets fails to lower the fractional chromatic number (OpenAI, linear list Hadwiger)
-- statement:
--   There is a $T$ such that the following holds for all reals $t \ge T$, $n$ and $r$ with $1 \le n \le t^{11/10}$ and $t/\log t \le r \le 4t$. Put
--   - $y = \max(1, t/r)$;
--   - $N = \lceil 192\, r \log(2y)\rceil$;
--   - $q = \lceil t/\lfloor r/200\rfloor\rceil^2$;
--   - $k = \lceil 10^6\cdot 65536\, t y\rceil$.
--
--   Let $G$ be a graph on at most $n$ vertices with $\chi_f(G) \le r$ (`number G ≤ r`). Let $E_0, \dots, E_{N-1}$ be vertex sets covering every vertex at least $N/2$ times. Suppose the thinning always fails: for every choice of stable sets $J_j$, deleting $\bigcup_j (J_j \cap E_j)$ leaves a graph with $\chi_f > r/2$. Then there are vertex sets $H$ and $U$ and $q$ pairwise disjoint sets $S_i \subseteq H \cap U$ with four properties:
--   - $H$ is $k$-connected;
--   - each $G[S_i]$ has $\chi_f > r/8$;
--   - every vertex of $H$ has at least $k/2$ neighbours in $H \setminus U$;
--   - $H \setminus U$ is $(k/32)$-connected.
--
--   `number` (the fractional chromatic number), `Stable` and `KConnectedOn` come from the definitions bundle `OAIQWLLH000` of this split. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.LinearListHadwiger.Sampling.source_thinning_failure_structure`, OpenAI's theorem of that name in `lean/OAI/Combinatorics/ListHadwiger/StageSampling.lean`.
-- source:
--   OpenAI, A linear list-coloring bound in terms of the Hadwiger number, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-linear-list-coloring-bound-in-terms-of-the-Hadwiger-number-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ListHadwiger/StageSampling.lean (declaration OAI.LinearListHadwiger.Sampling.source_thinning_failure_structure)

import Mathlib
import Definitions.Def_OAIQWLLH000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Sampling
open Filter Finset Fractional
attribute [local instance] Classical.propDecidable

theorem source_thinning_failure_structure :
    ∃ T : ℝ, ∀ t n r : ℝ, T ≤ t → 1 ≤ n → n ≤ t^(11/10:ℝ) →
      t/Real.log t ≤ r → r ≤ 4*t →
      let y := max 1 (t/r)
      let N := ⌈192*r*Real.log (2*y)⌉₊
      let q := ⌈t/(⌊r/200⌋₊:ℝ)⌉₊^2
      let k := ⌈(1000000*65536:ℝ)*t*y⌉₊
      ∀ (V : Type) [Fintype V] [DecidableEq V], ∀ G : SimpleGraph V,
      (Fintype.card V : ℝ) ≤ n → number G ≤ r →
      ∀ E : Fin N → Finset V,
      (∀ v, (N:ℝ)/2 ≤ (univ.filter (fun j => v∈E j)).card) →
      (∀ J : Fin N → Finset V, (∀ j, Stable G (J j)) →
        r/2 < number (G.induce
          (↑(univ\univ.biUnion (fun j => J j∩E j)) : Set V))) →
      ∃ (H U : Finset V) (S : Fin q → Finset V),
        KConnectedOn G H k ∧
        (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
        (∀ i, S i ⊆ H ∩ U) ∧
        (∀ i, r/8 < number (G.induce (↑(S i) : Set V))) ∧
        (∀ v∈H, k ≤ 2*((H\U).filter (G.Adj v)).card) ∧
        KConnectedOn G (H\U) (k/32) := by
  sorry

end LinearListHadwiger.Sampling

end OAI
end
