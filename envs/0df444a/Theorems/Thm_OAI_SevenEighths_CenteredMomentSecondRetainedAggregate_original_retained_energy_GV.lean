-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondRetainedAggregate_original_retained_energy_GV
-- name    : OAI.SevenEighths.CenteredMomentSecondRetainedAggregate.original_retained_energy_GV
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:22:48.615564+00:00
-- url     : https://prove2.me/theorems/de764518-bf55-4c1e-b015-14925ed5b0b5
-- title:
--   The second retained energy as a sum over common labels
-- statement:
--   For a `Character` $\eta$, $t$, finite $S$, $\beta$, Schwartz $W$ and reals $K>0$, $T_{\mathrm{sec}},Z,\xi$:
--   $$\texttt{secondRetainedEnergy}\,\eta\,t\,S\,\beta\,W\,K\,T_{\mathrm{sec}}\,Z\,\xi=\sum_{p}\texttt{heightCoeff}\,\eta\,t\,p_1\,\overline{\texttt{heightCoeff}\,\eta\,t\,p_2}\sum_{U}\sum_{h\in\mathcal O}[\texttt{canonicalPartition}\,p_1\,p_2\,U\,(g_Uh)]\,\texttt{sectorFrequency}(\dots,\texttt{physicalKernel}\,p_1\,p_2\,W\,K\,(\texttt{frequencyRadius}\,T_{\mathrm{sec}}\,Z\,\xi),(c\,g_U)\,h),$$
--   $p$ over `commonLabels` of the supported columns of $S$, $U$ over subsets of `CommonIndex p₁ p₂`, $g_U$ the nonunit and $c$ the common frequency generator.
--
--   Lean: `OAI.SevenEighths.CenteredMomentSecondRetainedAggregate.original_retained_energy_GV` in `lean/OAI/NumberTheory/DirichletL/Moments/SecondRetainedAggregate.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B028

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondRetainedAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentCanonicalFirst
open CenteredMomentSecondLocalization CenteredMomentSecondSourceRetained
open CenteredMomentSecondSectorFrequency CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentHeckeColumnWindow CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O

theorem original_retained_energy_GV (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ : ℝ) (hK : 0<K) :
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑ p : commonLabels (supportedColumns S) (supportedColumns S),
        heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
          ∑ U : Finset (CommonIndex p.val.1 p.val.2),∑' h : O,
            if canonicalPartition p.val.1 p.val.2 U
                (nonunitFrequencyGenerator p.val.1 p.val.2 U*h) then
              sectorFrequency η t S β p.val.1 p.val.2
                (commonLabels_supported S _ _ p.property).1
                (commonLabels_supported S _ _ p.property).2
                (physicalKernel p.val.1 p.val.2 W K (frequencyRadius Tsec Z ξ))
                ((commonFrequencyGenerator p.val.1 p.val.2*
                  nonunitFrequencyGenerator p.val.1 p.val.2 U)*h) else 0 := by
  sorry

end SevenEighths.CenteredMomentSecondRetainedAggregate

end

end OAI
end
