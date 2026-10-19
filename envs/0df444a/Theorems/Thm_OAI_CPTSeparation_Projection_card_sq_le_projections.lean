-- Prove2me | Theorems.Thm_OAI_CPTSeparation_Projection_card_sq_le_projections
-- name    : OAI.CPTSeparation.Projection.card_sq_le_projections
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T21:14:17.152982+00:00
-- url     : https://prove2.me/theorems/63a7ae03-8c05-4d71-b47b-dd8502729f06
-- title:
--   The discrete Loomis–Whitney inequality in three dimensions: |R|² ≤ |π_xy(R)|·|π_xz(R)|·|π_yz(R)| for a finite R ⊆ X × Y × Z
-- statement:
--   Let $X$, $Y$, $Z$ be finite types with decidable equality (`X Y Z : Type*` with `[Fintype X] [Fintype Y] [Fintype Z]` and `[DecidableEq X] [DecidableEq Y] [DecidableEq Z]`), and let $R \subseteq X \times Y \times Z$ be a finite set (`R : Finset (X × Y × Z)`). Write $\pi_{xy}(R)$, $\pi_{xz}(R)$ and $\pi_{yz}(R)$ for its images under the three coordinate projections to $X \times Y$, $X \times Z$ and $Y \times Z$ (`R.image (fun v => (v.1,v.2.1))` and so on). Then
--   $$|R|^2 \;\le\; |\pi_{xy}(R)| \cdot |\pi_{xz}(R)| \cdot |\pi_{yz}(R)| ,$$
--   an inequality of natural numbers.
--
--   This is the three-dimensional case of the discrete Loomis–Whitney inequality (Loomis–Whitney 1949): a finite set of lattice points is bounded in size by its three two-dimensional shadows.
--
--   Lean: `OAI.CPTSeparation.Projection.card_sq_le_projections`, OpenAI's theorem of that name in `lean/OAI/ModelTheory/Choiceless/Flows.lean`. The statement uses only Mathlib.
-- source:
--   L. H. Loomis and H. Whitney, An inequality related to the isoperimetric inequality, Bull. Amer. Math. Soc. 55 (1949), 961–962 (the Loomis–Whitney inequality). Lean proof: OpenAI, Choiceless polynomial time with counting does not capture polynomial time, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 243; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Choiceless-polynomial-time-with-counting-does-not-capture-polynomial-time-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/ModelTheory/Choiceless/Flows.lean (declaration OAI.CPTSeparation.Projection.card_sq_le_projections)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Projection

open Finset

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

theorem card_sq_le_projections (R : Finset (X × Y × Z)) :
    R.card^2 ≤ (R.image (fun v => (v.1,v.2.1))).card *
      (R.image (fun v => (v.1,v.2.2))).card * (R.image (fun v => (v.2.1,v.2.2))).card := by
  sorry

end CPTSeparation.Projection

end

end OAI
end
