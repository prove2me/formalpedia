-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_rescale_perspective_gap
-- name    : OAI.LeanBlast.CourtadeKumar.rescale_perspective_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:26:19.649175+00:00
-- url     : https://prove2.me/theorems/ccf01ad9-7bb6-4a43-b54c-37b6e0e75e45
-- title:
--   Rescaling a normalized perspective inequality to unnormalized weights
-- statement:
--   Let $\psi(v)=\frac{1+v}{2}\log(1+v)+\frac{1-v}{2}\log(1-v)$. Let $\iota$ be finite, $w,t,b:\iota\to\mathbb{R}$ with all $t_i>0$, and $T>0$, $k,C\in\mathbb{R}$. Suppose that, with weights $\frac{w_it_i}{T}$,
--   $$
--   \Bigl(\sum_i\frac{w_it_i}{T}\Bigl(\frac{b_i}{t_i}\Bigr)^2-\Bigl(\frac kT\Bigr)^2\Bigr)C\le2\Bigl(\sum_i\frac{w_it_i}{T}\psi\Bigl(\frac{b_i}{t_i}\Bigr)-\psi\Bigl(\frac kT\Bigr)\Bigr).
--   $$
--   Then
--   $$
--   \Bigl(\sum_i\frac{w_ib_i^2}{t_i}-\frac{k^2}{T}\Bigr)C\le2\Bigl(\sum_iw_it_i\,\psi\Bigl(\frac{b_i}{t_i}\Bigr)-T\,\psi\Bigl(\frac kT\Bigr)\Bigr).
--   $$
--
--   This turns a probability-weighted inequality into perspective form $t\,\psi(b/t)$, the form in which the two halves of a coordinate split are combined.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/JensenGaps.lean#L203-L223

import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_ComparisonEstimates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι]

theorem OAI.LeanBlast.CourtadeKumar.rescale_perspective_gap (w t b : ι → ℝ) (T k C : ℝ)
    (ht : ∀ i, 0 < t i) (hT : 0 < T)
    (hgap : ((∑ i, (w i * t i / T) * (b i / t i) ^ 2) - (k / T) ^ 2) * C ≤
      2 * ((∑ i, (w i * t i / T) * psi (b i / t i)) - psi (k / T))) :
    ((∑ i, w i * (b i) ^ 2 / t i) - k ^ 2 / T) * C ≤
      2 * ((∑ i, w i * t i * psi (b i / t i)) - T * psi (k / T)) := by sorry
