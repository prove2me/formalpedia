-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_r_pairEntropyGap_le_pairDissipation
-- name    : OAI.LeanBlast.CourtadeKumar.r_pairEntropyGap_le_pairDissipation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:59:54.681155+00:00
-- url     : https://prove2.me/theorems/6886b13a-3b64-4e02-8a38-1239d2e359f4
-- title:
--   Sharp production inequality for one coordinate
-- statement:
--   Let $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$ and $h(v)=\log2-\psi(v)$, the entropy in nats of a random sign with mean $v$. Let $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$, $\Delta(a,b)=h(a)-\frac12(h(a+b)+h(a-b))$ and $\delta(a,b)=\frac b2(\operatorname{artanh}(a+b)-\operatorname{artanh}(a-b))$. If $|a|+|b|<1$, then
--   $$
--   r\bigl(\Delta(a,b)\bigr)\le\delta(a,b).
--   $$
--
--   This is the one-dimensional case of the sharp production inequality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/PairEntropy.lean#L253-L265

import Mathlib
import Definitions.Def_SoftChannel204
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Model
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy__SoftChannel204

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar

theorem OAI.LeanBlast.CourtadeKumar.r_pairEntropyGap_le_pairDissipation (a b : ℝ) (h : |a| + |b| < 1) :
    r (pairEntropyGap a b) ≤ pairDissipation a b := by sorry
