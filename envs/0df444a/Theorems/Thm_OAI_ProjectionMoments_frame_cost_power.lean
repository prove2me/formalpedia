-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_frame_cost_power
-- name    : OAI.ProjectionMoments.frame_cost_power
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:56:20.146851+00:00
-- url     : https://prove2.me/theorems/28e8522d-10f4-4f4d-90e4-caca8b53e8e6
-- title:
--   Arithmetic consolidation of frame-moment constants
-- statement:
--   For natural numbers $1\le d$, $m\le d$, $n$ and reals $a$, $K\ge0$, $R>0$,
--   $$
--   2^m(\sqrt{2d})^{mn}\bigl(KR^{a-m}\bigr)^{n+1}R^m\,128^{dn}\le\Bigl(256^d\,(256\sqrt d)^{m(1-\frac1{n+1})}\,K\,R^{a-m(1-\frac1{n+1})}\Bigr)^{n+1}.
--   $$
--
--   It collects the constants of the frame moment bound into the power form used in the main estimate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/FrameMoments.lean#L149-L202

import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments

open OAI OAI.ProjectionMoments
open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology

theorem OAI.ProjectionMoments.frame_cost_power {d m n : ℕ} (hd : 1 ≤ d) (hm : m ≤ d)
    (a K R : ℝ) (hK : 0 ≤ K) (hR : 0 < R) :
    (2 : ℝ)^m * (Real.sqrt (2*d))^(m*n) *
      ((K*R^(a-m))^(n+1) * R^m * (128 : ℝ)^(d*n)) ≤
      ((256 : ℝ)^d * (256*Real.sqrt d)^((m:ℝ)*(1-1/((n:ℝ)+1))) * K *
        R^(a-(m:ℝ)*(1-1/((n:ℝ)+1))))^(n+1) := by sorry
