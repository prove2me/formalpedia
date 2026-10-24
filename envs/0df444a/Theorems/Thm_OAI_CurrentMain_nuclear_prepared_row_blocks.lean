-- Prove2me | Theorems.Thm_OAI_CurrentMain_nuclear_prepared_row_blocks
-- name    : OAI.CurrentMain.nuclear_prepared_row_blocks
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T22:14:17.085698+00:00
-- url     : https://prove2.me/theorems/36856ec4-6b56-47ff-95ef-1478d49f35c6
-- title:
--   Weighted matrix blocks from nuclearity, prepared for bistochastic tests (OpenAI uniform property Gamma, Proposition 4.3)
-- statement:
--   **Notation** (the published bundle `Def_UniformGamma` and the definitions bundle `OAIQWCMM000` of this split). Tracial states, the trace 2-norm $\lVert\cdot\rVert_{2,\tau}$ (`traceTwoNorm`), nuclearity and real rank zero are as in the statement `OAI.CurrentMain.finite_set_central_splitting`. The trace 1-norm is $\lVert a\rVert_{1,\tau} = \tau(|a|)$ (`traceOneNorm`).
--   - **Bistochastic tests.** A `BistochasticTest A` is a finite family $(v_i)$ in $A$ with $\sum_i v_i^* v_i = 1 = \sum_i v_i v_i^*$; `map ι` pushes it to $D$. Its energy at a trace $\tau$ and $y \in D$ is $\sum_i \lVert v_i y - y v_i\rVert_{2,\tau}^2$ (`energy`).
--   - **Averages.** `weightedAverage w v b` is $\sum_i w_i\, v_i b v_i^*$.
--   - **Rows.** A projection row over a projection $q$ (`ProjectionRow`) is a family $U_1, \dots, U_k \in D$ with $U_i^* U_i = q$ and $U_i^* U_j = 0$ for $i \ne j$. Its range is $p = \sum_i U_i q U_i^*$, and `matrix q H` is $\sum_{i,j} H_{ij}\, U_i q U_j^*$ for $H \in M_k(\mathbb C)$.
--   - **Block families.** A `WeightedBlockFamily r` is a finite family of weights $0 < w_j \le 1$, nonzero projections $q_j \le r$, sizes $k_j \ge 1$ and projection rows $U^{(j)}$ over $q_j$. Its ranges are $p_j$ (`range`) and its weighted sum is $\sum_j w_j p_j$ (`weightedSum`).
--
--   **The statement.** Let $A$ be a nuclear $C^*$-algebra, $\iota : A \to D$ a $*$-homomorphism into a $C^*$-algebra $D$ of real rank zero with at least one tracial state, $K$ a finite set of unitaries of $A$, $S$ a finite set of bistochastic tests on $A$, and $0 < \eta < 1$. Then there are $M \ge 1$, $0 < \sigma \le \eta$ with $M\sigma \le \eta$, a finite set $L \supseteq K$ of unitaries of $A$ and a bistochastic test $V$ on $A$ with:
--   1. for every $W \in S$, every finite family $(y_j)$ in $D$, every trace $\tau$ and every $B \ge 0$: if $\sum_j \lVert \iota(u) y_j - y_j \iota(u)\rVert_{2,\tau}^2 \le B$ for all $u \in L$, then $\sum_j \mathrm{energy}_\tau(\iota W, y_j) \le M B$;
--   2. for every projection $r \in D$ there is a weighted block family $F$ for $r$ such that:
--      - for each $j$ and $x \in L$, some $H \in M_{k_j}(\mathbb C)$ has $\lVert p_j\,\iota(x)\,p_j - \texttt{matrix}\ q_j\ H\rVert < \sigma$;
--      - for every $\tau$, $\bigl\lVert \sum_j w_j p_j - \sum_i \iota(v_i)\, r\, \iota(v_i)^* \bigr\rVert_{1,\tau} \le \eta^2$, where $(v_i)$ is $V$ with unit weights;
--      - for every $x \in L$ and $\tau$, $\sum_j w_j \lVert \iota(x) p_j - p_j \iota(x)\rVert_{2,\tau}^2 \le 6\sigma$.
--
--   This is the paper's Proposition 4.3 (weighted matrix blocks), prepared for the energy comparison of the given bistochastic tests.
--
--   Lean: `OAI.CurrentMain.nuclear_prepared_row_blocks`, OpenAI's theorem of that name (in `lean/OAI/Analysis/TracialSplitting/PreparedBlocks.lean`).
-- source:
--   OpenAI, Tracial projection methods and uniform property Gamma, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 291; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Tracial-projection-methods-and-uniform-property-Gamma-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/TracialSplitting/PreparedBlocks.lean (declaration OAI.CurrentMain.nuclear_prepared_row_blocks)

import Mathlib
import Definitions.Def_UniformGamma
import Definitions.Def_OAIQWCMM000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open Pureness

open scoped ComplexOrder

namespace CurrentMain

section Prepared

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem nuclear_prepared_row_blocks
    (hA : IsNuclear.{0,0} A) (ι : A →⋆ₐ[ℂ] D) (hRR : RealRankZero D)
    (hT : Nonempty (TracialState D)) (K : Finset (unitary A)) (S : Finset (BistochasticTest A))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ (M σ : ℝ) (L : Finset (unitary A)) (V : BistochasticTest A),
      1 ≤ M ∧ 0 < σ ∧ σ ≤ η ∧ M*σ ≤ η ∧ K ⊆ L ∧
      (∀ W ∈ S, ∀ (J : Type) [Fintype J] (y : J → D) (τ : TracialState D)
        (B : ℝ), 0 ≤ B →
        (∀ u ∈ L, ∑ j, traceTwoNorm τ (ι (u : A)*y j-y j*ι (u : A))^2 ≤ B) →
        ∑ j, (W.map ι).energy τ (y j) ≤ M*B) ∧
      ∀ r : D, IsStarProjection r → ∃ F : WeightedBlockFamily r,
        (∀ j, ∀ x ∈ L, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
          ‖F.range j*ι (x : A)*F.range j-(F.row j).matrix (F.base j) H‖ < σ) ∧
        (∀ τ : TracialState D,
          traceOneNorm τ (F.weightedSum-weightedAverage (fun _ => (1 : ℝ)) (V.map ι).coeff r) ≤ η^2) ∧
        (∀ x ∈ L, ∀ τ : TracialState D,
          ∑ j, F.weight j*traceTwoNorm τ (ι (x : A)*F.range j-F.range j*ι (x : A))^2 ≤ 6*σ) := by
  sorry

end Prepared

end CurrentMain

end

end

end OAI
end
