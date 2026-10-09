-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_sourceTruncation_eq_canonical
-- name    : OAI.SevenEighths.ProbeGramCommon.sourceTruncation_eq_canonical
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:26:56.928776+00:00
-- url     : https://prove2.me/theorems/a8ed9748-b55c-4475-a025-36a003065cbe
-- title:
--   The source truncation equals the canonical sum
-- statement:
--   For a finite set $S$ of maximal ideals containing `fixedBadPrimes`, $\sigma$, finite sets $F$ of supported ideals and $E$ of Gram frequencies, compactly supported $W$, $Y,Q>0$, Schwartz $U$ and $v$: `sourceTruncation S hS σ F E W hW Y Q hY U v` $=$ `sourceCanonicalSum S hS σ F (fun _ => E) W hW Y Q hY U v`.
--
--   Lean: `OAI.SevenEighths.ProbeGramCommon.sourceTruncation_eq_canonical` in `lean/OAI/NumberTheory/DirichletL/Detector/GramTruncation.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem sourceTruncation_eq_canonical (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (F : Finset SupportedIdeal) (E : Finset GramFrequency)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    sourceTruncation S hS σ F E W hW Y Q hY U v=sourceCanonicalSum S hS σ F (fun _=>E) W hW Y Q hY U v := by
  sorry

end SevenEighths.ProbeGramCommon
end

end OAI
end
