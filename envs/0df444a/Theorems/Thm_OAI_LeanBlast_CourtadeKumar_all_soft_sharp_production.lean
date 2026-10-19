-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_all_soft_sharp_production
-- name    : OAI.LeanBlast.CourtadeKumar.all_soft_sharp_production
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T15:26:40.880229+00:00
-- url     : https://prove2.me/theorems/4e5c937e-87f1-422f-acf4-247818ff71ee
-- title:
--   Sharp production inequality on the Boolean cube
-- statement:
--   On the Boolean cube $\{0,1\}^n$ let $\mathbb E$ be the uniform average. Let $h(v)=\log2-\psi(v)$ with $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, the entropy in nats of a random sign with mean $v$, and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$. A function $g$ is interior if $-1<g<1$ everywhere, its information is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and its dissipation is $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ with $\partial_ig(x)=\frac12(g(x)-g(x^{\oplus i}))$.
--
--   For every interior $g:\{0,1\}^n\to(-1,1)$,
--   $$
--   r\bigl(I(g)\bigr)\le\mathcal D(g).
--   $$
--
--   The rate $r$ is the exact production of the soft dictators, so the inequality is sharp. Along the noise semigroup it yields the soft contraction of information.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/SoftChannel/Production.lean#L99-L129

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
open scoped BigOperators Topology

theorem OAI.LeanBlast.CourtadeKumar.all_soft_sharp_production {n : ℕ} (g : Cube n → ℝ) (hg : IsInterior g) :
    r (informationDeficit g) ≤ dissipation g := by sorry
