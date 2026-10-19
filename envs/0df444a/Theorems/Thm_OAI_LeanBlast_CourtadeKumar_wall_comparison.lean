-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_wall_comparison
-- name    : OAI.LeanBlast.CourtadeKumar.wall_comparison
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T15:21:59.022687+00:00
-- url     : https://prove2.me/theorems/eafb89f8-419b-4b1f-a437-502b378d80af
-- title:
--   The wall demand increases with the mean
-- statement:
--   Let $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, let $h(v)=\log2-\psi(v)$ be the entropy in nats of a random sign with mean $v$, and let $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$ be the rate function, with derivative $r'$. Let $H_2(m,d)=\frac12(h(m+d)+h(m-d))$ and let the wall demand be $W(m,d,e)=r(h(m)-e)-r(H_2(m,d)-e)$. Let $0\le m\le w$, $d\ge0$, $w+d<1$, $0<e<H_2(w,d)$, and $h(m)-e\le\psi(0.77)$. Then
--   $$
--   W(m,d,e)\le W(w,d,e).
--   $$
--
--   Below the soft cutoff, moving the mean away from $0$ can only increase the demand on the dissipation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/SoftChannel/Wall.lean#L181-L203

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
import Definitions.Def_OAI_InformationTheory_SoftChannel_HighReserve
import Definitions.Def_OAI_InformationTheory_SoftChannel_RateSlope
import Definitions.Def_OAI_InformationTheory_SoftChannel_Wall

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped Topology

theorem OAI.LeanBlast.CourtadeKumar.wall_comparison {m w d e : ℝ} (hm : 0 ≤ m) (hmw : m ≤ w) (hd : 0 ≤ d) (hwd : w+d<1)
    (he : 0 < e) (hj : e < pairH w d) (hI : entropy m-e ≤ softCutoff) :
    wallDemand m d e ≤ wallDemand w d e := by sorry
