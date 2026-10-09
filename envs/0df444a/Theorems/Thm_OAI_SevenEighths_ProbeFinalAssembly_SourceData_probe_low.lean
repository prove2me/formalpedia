-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeFinalAssembly_SourceData_probe_low
-- name    : OAI.SevenEighths.ProbeFinalAssembly.SourceData.probe_low
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:16:12.266784+00:00
-- url     : https://prove2.me/theorems/539744d4-dcfc-4b09-b51a-5fb8a4bbacc8
-- title:
--   The source probe grows at most like Z^(3/16+loss)
-- statement:
--   For every `HighData Δ` $D$, every `SourceData D` $F$, every `loss` $>0$ and every `Character` $\eta$, $Z\mapsto F.\texttt{probe}\,\eta\,Z$ is $O(Z^{3/16+\mathrm{loss}})$ as $Z\to\infty$.
--
--   Lean: `OAI.SevenEighths.ProbeFinalAssembly.SourceData.probe_low` in `lean/OAI/NumberTheory/DirichletL/Detector/FinalAssemblyData.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
local notation "O" => HeckeFamily.O

theorem SourceData.probe_low {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (loss : ℝ) (hloss : 0<loss) (η : Character) :
    F.probe η=O[atTop](fun Z : ℝ=>Z^(3/16+loss)) := by
  sorry

end SevenEighths.ProbeFinalAssembly

end

end OAI
end
