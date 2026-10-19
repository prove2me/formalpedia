-- Prove2me | Theorems.Thm_OAI_CPTSeparation_Grid_grid_hf_transfer
-- name    : OAI.CPTSeparation.Grid.grid_hf_transfer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T21:18:45.9523+00:00
-- url     : https://prove2.me/theorems/e073d392-faf8-4f8f-8600-7394f29d6f54
-- title:
--   Counting formulas cannot distinguish the two grid structures on bounded hereditarily finite tuples (OpenAI, choiceless polynomial time)
-- statement:
--   Let $n \ge 1$ (`hn`), $s > 0$ (`hs`), $m > 0$ (`hm`) and $M$ be natural numbers, and let `vstar : Vertex n` be a vertex. Consider the two analysis structures `analysisStructure (0 : Vertex n → Scalar)` and `analysisStructure (Pi.single vstar 1)` over $\mathbb{F}_3$ (`Scalar` is `ZMod 3`). They are the right-hand side $0$ and the right-hand side with a single $1$ at `vstar`. Assume both atom types are nonempty (`[Nonempty (Atom (0 : Vertex n → Scalar))]` and `[Nonempty (Atom (Pi.single vstar 1))]`), and assume:
--
--   1. (`hwidth`) $\max(4, m+1)\cdot s \le M$;
--   2. (`hhom`) $7\max(2,m)s + 7\bigl(6\max(2,m)s/\mathrm{boxConstant}\bigr)^{3/2} + 1 \le M$, in $\mathbb{R}$, with `boxConstant` from the bundle;
--   3. (`hgiant`) `GiantBound n M`.
--
--   Let $\varphi$ be a counting formula over the hereditarily finite relation vocabulary with $m$ parameters and no other free variables (`φ : Counting.Formula (Forms.HFRelation AnalysisSymbol) (Fin m)` with `hφ : φ.free = ∅`). Let $v$ and $w$ be $m$-tuples of elements of the bounded hereditarily finite domains over the respective atoms (`Forms.Domain (A := Atom …) (CentralGroup n) s`). Then $\varphi$ holds of $v$ in the hereditarily finite expansion of the first structure (`Forms.hfStructure`) if and only if it holds of $w$ in that of the second.
--
--   `Vertex`, `Atom`, `analysisStructure`, `AnalysisSymbol`, `CentralGroup`, `GiantBound`, `boxConstant` and the `Forms` and `Counting` definitions come from the definitions bundle `OAIQWCPT000` of this split and the published bundle `Def_ChoicelessPolynomialTime`. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.CPTSeparation.Grid.grid_hf_transfer`, OpenAI's theorem of that name in `lean/OAI/ModelTheory/Choiceless/Forms.lean`.
-- source:
--   OpenAI, Choiceless polynomial time with counting does not capture polynomial time, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 243; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Choiceless-polynomial-time-with-counting-does-not-capture-polynomial-time-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/ModelTheory/Choiceless/Forms.lean (declaration OAI.CPTSeparation.Grid.grid_hf_transfer)

import Mathlib
import Definitions.Def_ChoicelessPolynomialTime
import Definitions.Def_OAIQWCPT000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Grid

open Classical Finset

variable {n M m s : ℕ} {b : Vertex n → Scalar}

theorem grid_hf_transfer (hn : 1 ≤ n) (hs : 0 < s) (hm : 0 < m)
    (vstar : Vertex n) [Nonempty (Atom (0 : Vertex n → Scalar))]
    [Nonempty (Atom (Pi.single vstar 1))]
    (hwidth : max 4 (m+1)*s ≤ M)
    (hhom : (7*(max 2 m*s):ℝ)+7*((6*(max 2 m*s):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M)
    (φ : Counting.Formula (Forms.HFRelation AnalysisSymbol) (Fin m)) (hφ : φ.free = ∅)
    (v : Fin m → Forms.Domain (A := Atom (0 : Vertex n → Scalar)) (CentralGroup n) s)
    (w : Fin m → Forms.Domain (A := Atom (Pi.single vstar 1)) (CentralGroup n) s) :
    φ.eval (Forms.hfStructure (analysisStructure (0 : Vertex n → Scalar))) v ↔
      φ.eval (Forms.hfStructure (analysisStructure (Pi.single vstar 1))) w := by
  sorry

end CPTSeparation.Grid

end

end OAI
end
