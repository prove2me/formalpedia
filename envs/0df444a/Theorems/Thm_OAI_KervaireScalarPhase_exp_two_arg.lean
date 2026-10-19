-- Prove2me | Theorems.Thm_OAI_KervaireScalarPhase_exp_two_arg
-- name    : OAI.KervaireScalarPhase.exp_two_arg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:39:04.822299+00:00
-- url     : https://prove2.me/theorems/0b83db1c-b8d8-4386-9c97-6b44d55e586e
-- title:
--   Doubling the argument
-- statement:
--   For every nonzero complex number $x$,
--   $$
--   e^{2i\arg x}=\frac x{\bar x}.
--   $$
--
--   The quotient $x/\bar x$ is the unit complex number with twice the argument of $x$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/ScalarPhase.lean#L56-L70

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase

open OAI OAI.KervaireScalarPhase
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

theorem OAI.KervaireScalarPhase.exp_two_arg (x : ℂ) (hx : x ≠ 0) :
    Complex.exp ((2 * x.arg : ℝ) * Complex.I) = x / star x := by sorry
