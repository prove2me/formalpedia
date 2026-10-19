-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_low_information_joining
-- name    : OAI.LeanBlast.CourtadeKumar.low_information_joining
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T15:22:37.291486+00:00
-- url     : https://prove2.me/theorems/5a7d2548-e8ef-4db5-9839-913e7c7301d0
-- title:
--   Joining two halves with low information
-- statement:
--   On the Boolean cube $\{0,1\}^n$ let $\mathbb E$ be the uniform average. Let $h(v)=\log2-\psi(v)$ with $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, the entropy in nats of a random sign with mean $v$, and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$. A function $g$ is interior if $-1<g<1$ everywhere, its information is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and its dissipation is $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ with $\partial_ig(x)=\frac12(g(x)-g(x^{\oplus i}))$.
--
--   Let $A,B$ be interior functions on $\{0,1\}^n$ with means $m\pm d$, where $m>0$, $d>0$, $m+d<1$. Let $e=\frac12(\mathbb Eh(A)+\mathbb Eh(B))$, and suppose $e\le\frac12(h(m+d)+h(m-d))$ and $h(m)-e\le\psi(0.77)$. Then the wall demand is paid by the joining cost:
--   $$
--   r\bigl(h(m)-e\bigr)-r\Bigl(\tfrac12\bigl(h(m+d)+h(m-d)\bigr)-e\Bigr)\le\mathbb E\Bigl[\frac{A-B}4\bigl(\operatorname{artanh}A-\operatorname{artanh}B\bigr)\Bigr].
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/SoftChannel/Joining.lean#L83-L109

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

theorem OAI.LeanBlast.CourtadeKumar.low_information_joining {n : ℕ} (A B : Cube n → ℝ) (hA : IsInterior A) (hB : IsInterior B)
    {m d : ℝ} (hm : 0 < m) (hd : 0 < d) (hmd : m+d<1)
    (ha : cubeAverage A=m+d) (hb : cubeAverage B=m-d)
    (hphys : (entropyAverage A+entropyAverage B)/2 ≤ pairH m d)
    (hI : entropy m-(entropyAverage A+entropyAverage B)/2 ≤ softCutoff) :
    wallDemand m d ((entropyAverage A+entropyAverage B)/2) ≤
      cubeAverage (fun x => joiningCost (A x) (B x)) := by sorry
