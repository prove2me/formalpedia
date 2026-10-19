-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_common_output_payment
-- name    : OAI.LeanBlast.CourtadeKumar.common_output_payment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T15:20:05.232869+00:00
-- url     : https://prove2.me/theorems/2fce91ba-49ee-48cd-88c4-7cdced26ecf0
-- title:
--   Thinning toward a common output pays for itself
-- statement:
--   Let $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, let $h(v)=\log2-\psi(v)$ be the entropy in nats of a random sign with mean $v$, and let $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$ be the rate function, with derivative $r'$. For a pair $(c,d)$ and $l\in(0,1]$ let $x_l=1-l(1-c)$, $H_2(c,d)=\frac12(h(c+d)+h(c-d))$,
--   $$
--   I_l=h(x_l)-l\,H_2(c,d),\qquad J_l=H_2(x_l,ld)-l\,H_2(c,d).
--   $$
--   If $c\ge0$, $d>0$ and $c+d<1$, then $r(I_l)-r(J_l)\le l\,r\bigl(h(c)-H_2(c,d)\bigr)$.
--
--   So partially thinning a pair costs at most a proportional share of the rate of the full pair entropy gap.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/SoftChannel/Payment.lean#L250-L278

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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveInequality__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Comparison__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment__SoftChannel204
import Definitions.Def_OAI_InformationTheory_SoftChannel_Canonical
import Definitions.Def_OAI_InformationTheory_SoftChannel_Thinning
import Definitions.Def_OAI_InformationTheory_SoftChannel_Payment

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter MeasureTheory
open scoped Topology
open SoftChannel204

theorem OAI.LeanBlast.CourtadeKumar.common_output_payment {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) :
    r (thinI c d l)-r (thinJ c d l) ≤ l*r (pairEntropyGap c d) := by sorry
