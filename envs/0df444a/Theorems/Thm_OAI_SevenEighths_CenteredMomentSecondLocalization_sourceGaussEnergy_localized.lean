-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondLocalization_sourceGaussEnergy_localized
-- name    : OAI.SevenEighths.CenteredMomentSecondLocalization.sourceGaussEnergy_localized
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:16:44.52283+00:00
-- url     : https://prove2.me/theorems/a92f503b-40ed-4ce8-9675-1f2093bda8db
-- title:
--   The source Gauss energy: zero, retained and discarded parts
-- statement:
--   For $\eta$, $t$, $S$, $\beta$, a Schwartz $W$ and reals $K>0$, $T_{\mathrm{sec}},Z,\xi$: `sourceGaussEnergy S β (heightCoeff η t) W K` $=K\,\widehat W_{\mathrm{rad}}(0)\cdot$`sourceSecondZero S β η t` $+$ `secondRetainedEnergy η t S β W K Tsec Z ξ` $+$ `secondDiscardedEnergy η t S β W K Tsec Z ξ`, with $\widehat W_{\mathrm{rad}}$ = `paperRadialFourier W`.
--
--   Lean: `OAI.SevenEighths.CenteredMomentSecondLocalization.sourceGaussEnergy_localized` in `lean/OAI/NumberTheory/DirichletL/Moments/SecondLocalization.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022
import Definitions.Def_OAIHecke78B023

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondLocalization
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentSecondWholeKernel CenteredMomentSecondTail
open CenteredMomentSectorLocalization CenteredMomentSupportedCorrelation
open CenteredMomentSupportedTailAggregate CenteredMomentSourceSecondZeroEnergy CenteredMomentSecondDiagonal
local notation "O" => ActualEisensteinCubic.O

theorem sourceGaussEnergy_localized (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    CenteredMomentOriginalChildEnergy.sourceGaussEnergy S β (heightCoeff η t) W K=
      ((K:ℂ)*paperRadialFourier W 0)*sourceSecondZero S β η t+
      secondRetainedEnergy η t S β W K Tsec Z ξ+
      secondDiscardedEnergy η t S β W K Tsec Z ξ := by
  sorry

end SevenEighths.CenteredMomentSecondLocalization

end

end OAI
end
