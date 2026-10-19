-- Prove2me | Theorems.Thm_OAI_KervaireScalarPhase_phase_eq_arg_one_sub
-- name    : OAI.KervaireScalarPhase.phase_eq_arg_one_sub
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:39:33.912353+00:00
-- url     : https://prove2.me/theorems/89f3d67f-4b00-4f48-aa2c-544db90d53ef
-- title:
--   The fractional phase through $\arg(1-z)$
-- statement:
--   For $z\in\mathbb C$ let $\mathrm{ph}(z)\in[0,1)$ be the fractional part of $\arg z/2\pi$, and for $|a|<1$ let $\mathrm{ph}_a(z)=\frac12+\arg(1-az)/\pi$. For every $z$ on the unit circle with $z\ne1$,
--   $$
--   \mathrm{ph}(z)=\frac12+\frac{\arg(1-z)}\pi .
--   $$
--
--   So the fractional phase is the limit of the smooth phases $\mathrm{ph}_a$ at $a=1$, away from the cut.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/ScalarPhase.lean#L72-L118

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

theorem OAI.KervaireScalarPhase.phase_eq_arg_one_sub {z : ℂ} (hz : ‖z‖ = 1) (hz' : z ≠ 1) :
    phase z = 1 / 2 + (1 - z).arg / Real.pi := by sorry
