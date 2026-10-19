-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_concaveOn_logCorrectedPerspective
-- name    : OAI.LeanBlast.CourtadeKumar.concaveOn_logCorrectedPerspective
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:32:59.836062+00:00
-- url     : https://prove2.me/theorems/7a484845-2785-4f0d-a4ba-a4b74e513e46
-- title:
--   Concavity of the log-corrected perspective $v\mapsto v f(x/v)-Cv\log v$
-- statement:
--   Let $f,f',f'':\mathbb{R}\to\mathbb{R}$, and let $x>0$, $C\in\mathbb{R}$ and $j>0$ (a join point). Assume:
--
--   1. $f$ has derivative $f'(y)$ at every $y>0$, and $f'$ is continuous on $(0,\infty)$;
--   2. $f'$ has derivative $f''(y)$ at every $y>0$ with $y\ne j$;
--   3. $y^2f''(y)\le C$ for every $y>0$ with $y\ne j$.
--
--   Then the function
--   $$
--   v\longmapsto v\,f\Bigl(\frac xv\Bigr)-C\,v\log v
--   $$
--   is concave on $(0,\infty)$.
--
--   The curvature bound $y^2f''(y)\le C$ on the original function exactly compensates the logarithmic correction. This is how curvature estimates for $L$ and $K$ become concavity statements used in the inductive inequality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/PerspectiveCalculus.lean#L72-L96

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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set

theorem OAI.LeanBlast.CourtadeKumar.concaveOn_logCorrectedPerspective (f f' f'' : ℝ → ℝ)
    (x C join : ℝ) (hx : 0 < x) (hjoin : 0 < join)
    (hf : ∀ y, 0 < y → HasDerivAt f (f' y) y)
    (hcf' : ContinuousOn f' (Ioi 0))
    (hf' : ∀ y, 0 < y → y ≠ join → HasDerivAt f' (f'' y) y)
    (hcurv : ∀ y, 0 < y → y ≠ join → y ^ 2 * f'' y ≤ C) :
    ConcaveOn ℝ (Ioi 0) (logCorrectedPerspective f x C) := by sorry
