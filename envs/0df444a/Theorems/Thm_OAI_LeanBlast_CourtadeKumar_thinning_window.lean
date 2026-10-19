-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_thinning_window
-- name    : OAI.LeanBlast.CourtadeKumar.thinning_window
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T15:18:09.179281+00:00
-- url     : https://prove2.me/theorems/0e2ae82d-d447-4d32-bbe9-76824d15707d
-- title:
--   The thinning window integral
-- statement:
--   Let $c_\beta(v)=\max(v-\beta,0)/v^2$ be the clipped kernel. Let $h(v)$ be the entropy in nats of a random sign with mean $v$, and $\psi(v)=\log2-h(v)$. Let $0\le x$, $d>0$, $x+d<1$, and let $e$ satisfy
--   $$
--   (1-x)\,h\Bigl(\frac d{1-x}\Bigr)\le e\le\frac{h(x+d)+h(x-d)}2 .
--   $$
--   Then the integral of $c_{\log(1+x)}$ over $\bigl[e+\psi(x),\ e+\log2-\frac{h(x+d)+h(x-d)}2\bigr]$ is at most $-\frac32\log\bigl(1-d^2/(1+x)^2\bigr)$.
--
--   This is the window estimate used when a symmetric pair of means is thinned toward the common output $+1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/SoftChannel/Window.lean#L92-L129

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

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set MeasureTheory
open scoped Topology
open SoftChannel204

theorem OAI.LeanBlast.CourtadeKumar.thinning_window {x d e : ℝ} (hx : 0 ≤ x) (hd : 0 < d) (hxd : x+d < 1)
    (hefloor : (1-x)*entropy (d/(1-x)) ≤ e)
    (hehi : e ≤ (entropy (x+d)+entropy (x-d))/2) :
    (∫ h in (e+psi x)..(e+ell-(entropy (x+d)+entropy (x-d))/2),
      clipKernel (Real.log (1+x)) h) ≤
      -(3/2:ℝ)*Real.log (1-d^2/(1+x)^2) := by sorry
