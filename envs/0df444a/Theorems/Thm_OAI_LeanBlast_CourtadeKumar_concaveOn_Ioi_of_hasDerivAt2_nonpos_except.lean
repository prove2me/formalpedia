-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_concaveOn_Ioi_of_hasDerivAt2_nonpos_except
-- name    : OAI.LeanBlast.CourtadeKumar.concaveOn_Ioi_of_hasDerivAt2_nonpos_except
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:31:14.058898+00:00
-- url     : https://prove2.me/theorems/d26a8e9f-1c61-4bae-8aff-7f4cee7fc578
-- title:
--   Concavity from a nonpositive second derivative outside one point
-- statement:
--   Let $f,f',f'':\mathbb{R}\to\mathbb{R}$ and $a,c\in\mathbb{R}$. Assume:
--
--   1. $f$ has derivative $f'(x)$ at every $x>a$;
--   2. $f'$ is continuous on $(a,\infty)$;
--   3. $f'$ has derivative $f''(x)$ at every $x>a$ with $x\ne c$, and $f''(x)\le0$ there.
--
--   Then $f$ is concave on $(a,\infty)$: for $x,y>a$ and $\alpha\in[0,1]$,
--   $$
--   f\bigl(\alpha x+(1-\alpha)y\bigr)\ge\alpha f(x)+(1-\alpha)f(y).
--   $$
--
--   The exceptional point allows functions glued at a join point, such as the tangent-line extension $K$, whose second derivative jumps there.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/ConcavityAcrossJoin.lean#L42-L59

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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance
import Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set

theorem OAI.LeanBlast.CourtadeKumar.concaveOn_Ioi_of_hasDerivAt2_nonpos_except
    (f f' f'' : ℝ → ℝ) (a c : ℝ)
    (hd : ∀ x, a < x → HasDerivAt f (f' x) x)
    (hcf' : ContinuousOn f' (Ioi a))
    (hd' : ∀ x, a < x → x ≠ c → HasDerivAt f' (f'' x) x)
    (hneg : ∀ x, a < x → x ≠ c → f'' x ≤ 0) :
    ConcaveOn ℝ (Ioi a) f := by sorry
