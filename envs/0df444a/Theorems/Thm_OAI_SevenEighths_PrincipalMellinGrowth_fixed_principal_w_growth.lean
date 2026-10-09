-- Prove2me | Theorems.Thm_OAI_SevenEighths_PrincipalMellinGrowth_fixed_principal_w_growth
-- name    : OAI.SevenEighths.PrincipalMellinGrowth.fixed_principal_w_growth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:54:39.467013+00:00
-- url     : https://prove2.me/theorems/c10469af-49e3-4cf0-a0d4-4c5d888f3038
-- title:
--   Growth of the pole-removed principal L-function
-- statement:
--   Let $M$ be a nonzero ideal of $\mathcal O$ (`HeckeFamily.O`), $c_w>1$, $x\in[19/20,c_w]$ and $t\in\mathbb R$. Then $\|\texttt{HeckeOrigin.poleRemoved}\,(\texttt{fixedPrincipal}\,M)\,(x+it)\|\le\texttt{wAmplitude}\,M\,c_w\cdot\texttt{height}(t)^3$.
--
--   Lean: `OAI.SevenEighths.PrincipalMellinGrowth.fixed_principal_w_growth` in `lean/OAI/NumberTheory/DirichletL/PrincipalMellinGrowth.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B019

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Complex Set
namespace SevenEighths.PrincipalMellinGrowth
open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary

theorem fixed_principal_w_growth (M : Ideal HeckeFamily.O) [NeZero M]
    {cw : ℝ} (hcw : 1<cw) {x : ℝ} (hx : x∈Icc (19/20 : ℝ) cw) (t : ℝ) :
    ‖HeckeOrigin.poleRemoved (fixedPrincipal M) ((x:ℂ)+t*I)‖≤wAmplitude M cw*height t^3 := by
  sorry

end SevenEighths.PrincipalMellinGrowth

end

end OAI
end
