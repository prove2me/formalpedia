-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_cubeAverage_signProbability
-- name    : OAI.LeanBlast.CourtadeKumar.cubeAverage_signProbability
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T15:02:54.712901+00:00
-- url     : https://prove2.me/theorems/c3017a39-316b-4751-a05c-5e6d94f1a665
-- title:
--   Averaging commutes with sign probabilities
-- statement:
--   On the Boolean cube $\{0,1\}^n$, $\mathbb Eg=2^{-n}\sum_xg(x)$ is the uniform average and $T_u$ is the noise operator with kernel $K_u(x,y)=\prod_i\frac{1\pm u}2$, with the sign $+$ when $x_i=y_i$. The sign law with mean $v$ gives the bit $b$ probability $p_v(b)=\frac{1+v}2$ if $b$ is true and $\frac{1-v}2$ otherwise.
--
--   For every soft function $g$ on the cube and bit $b$,
--   $$
--   \mathbb E\,p_{g(x)}(b)=p_{\mathbb Eg}(b).
--   $$
--
--   So the marginal law of the output bit of a soft channel is the sign law of the mean of $g$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/FiniteDistribution.lean#L42-L56

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

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators
variable {n : ℕ}

theorem OAI.LeanBlast.CourtadeKumar.cubeAverage_signProbability (g : Cube n → ℝ) (b : Bool) :
    cubeAverage (fun x => signProbability (g x) b) = signProbability (cubeAverage g) b := by sorry
