-- Prove2me | Theorems.Thm_OAI_ThermalDual_defect_young
-- name    : OAI.ThermalDual.defect_young
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:47:51.45013+00:00
-- url     : https://prove2.me/theorems/01e3eaff-e504-4c01-a680-7c5b690f5ddd
-- title:
--   A Young-type absorption inequality for a perturbed defect bound
-- statement:
--   Let $x,a,m,C,\kappa,\varepsilon$ be real numbers with $x\ge0$, $a\ge0$, $m\ge0$, $C>0$, $\kappa\ge0$, $\varepsilon>0$, and suppose
--   $$\kappa\le\frac{\varepsilon^2}{4(\varepsilon+2)C^2}\qquad\text{and}\qquad x\le a+\sqrt{2\kappa}\,C\,m .$$
--   Then
--   $$x^2\le a^2+\frac\varepsilon2\bigl(a^2+m^2\bigr).$$
--
--   So a bound $x\le a+(\text{small})\cdot m$ with a perturbation coefficient $\sqrt{2\kappa}C$ that is small relative to $\varepsilon$ yields a squared bound with only an $\varepsilon/2$ relative loss. It is used to absorb the output-replacement error term, of size $\sqrt{2\kappa}$, into an arbitrarily small multiplicative slack.
--
--   **Formalization Note** The hypotheses $a\ge0$ and $m\ge0$ appear in the Lean statement (as unused named hypotheses); the argument needs only $x\ge0$, $C>0$, $\kappa\ge0$, $\varepsilon>0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Duality.lean#L374-L393

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

open OAI
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology Complex MeasureTheory
variable {I J : Type*} [Fintype I] [Fintype J]

theorem OAI.ThermalDual.defect_young {x a m C κ ε : ℝ}
    (hx : 0 ≤ x) (_ha : 0 ≤ a) (_hm : 0 ≤ m) (hC : 0 < C) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hk : κ ≤ ε^2/(4*(ε+2)*C^2))
    (ht : x ≤ a+Real.sqrt (2*κ)*C*m) :
    x^2 ≤ a^2+ε/2*(a^2+m^2) := by sorry
