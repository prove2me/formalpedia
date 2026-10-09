-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_original_energy_common_blocks
-- name    : OAI.SevenEighths.ProbeGramCommon.original_energy_common_blocks
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:26:08.125987+00:00
-- url     : https://prove2.me/theorems/b5b61ecd-b5a1-4a38-a892-4eff8932bb48
-- title:
--   The low Gauss energy as zero mode plus common blocks
-- statement:
--   For a finite set $S$ of maximal ideals, $\sigma$, compactly supported $W$, $Y,Q>0$, Schwartz $U$ and $v$: `gaussEnergy (lowGaussColumns W hW Y hY) … (lowGaussColumn (calibrationForSet S hS) W Y σ v) U Q` equals `lowGramZeroMode … σ v U Q` plus $\frac Q{Y^3}\sum_{C\in\texttt{commonPool}}\sum_{k}$`originalCommonBlock S hS σ C k W hW Y Q hY U v` (the inner sum a `tsum` over Gram frequencies).
--
--   Lean: `OAI.SevenEighths.ProbeGramCommon.original_energy_common_blocks` in `lean/OAI/NumberTheory/DirichletL/Detector/GramCommonEnergy.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT RayFourExpansion
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem original_energy_common_blocks (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    gaussEnergy (lowGaussColumns W hW Y hY) (fun I=>primaryGenerator I.val)
      (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
      (lowGaussColumn (calibrationForSet S hS) W Y σ v) U Q=
      lowGramZeroMode (calibrationForSet S hS) W hW Y hY σ v U Q+
      ((Q/Y^3:ℝ):ℂ)*(∑C∈commonPool (lowGaussColumns W hW Y hY),
        ∑'k : GramFrequency,originalCommonBlock S hS σ C k W hW Y Q hY U v) := by
  sorry

end SevenEighths.ProbeGramCommon
end

end OAI
end
