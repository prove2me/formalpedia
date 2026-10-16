-- Prove2me | Theorems.Thm_OAI_WeightedGenerator_negative_quartic_bounded
-- name    : OAI.WeightedGenerator.negative_quartic_bounded
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:58:11.514977+00:00
-- url     : https://prove2.me/theorems/602216d8-bb17-4a90-95f4-4a003bb1745c
-- title:
--   A quartic with leading coefficient $-4$ is bounded above on $[0,\infty)$
-- statement:
--   For all real numbers $a,b,c,d$ there is a constant $C\in\mathbb{R}$ such that
--   $$-4t^4+a\,t^3+b\,t^2+c\,t+d\le C\qquad\text{for every }t\ge0 .$$
--
--   This elementary bound is used to show that the drift of the regularizing quartic moment under the thermal-noise generator, which is a polynomial of degree four in the photon number with negative leading coefficient, is bounded above uniformly over states.
--
--   **Formalization Note** The proof exhibits the explicit constant $C=S(S^3+S^2+S+1)$ with $S=1+|a|+|b|+|c|+|d|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Minimum.lean#L907-L961

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Contraction
import Definitions.Def_OAI_InformationTheory_PhotonNumber_FiniteVariation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_PhysicalMinimum
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Duality
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Minimum

open OAI OAI.WeightedGenerator
open scoped BigOperators

theorem OAI.WeightedGenerator.negative_quartic_bounded (a b c d : ℝ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → -4*t^4+a*t^3+b*t^2+c*t+d ≤ C := by sorry
