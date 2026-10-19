-- Prove2me | Theorems.Thm_OAI_KervaireScalarPhase_tendsto_smoothPhase_cut
-- name    : OAI.KervaireScalarPhase.tendsto_smoothPhase_cut
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:40:05.981214+00:00
-- url     : https://prove2.me/theorems/18d9d362-d6ae-428a-9d21-ec780f04cfa6
-- title:
--   Smooth phases converge to the fractional phase
-- statement:
--   For $z\in\mathbb C$ let $\mathrm{ph}(z)\in[0,1)$ be the fractional part of $\arg z/2\pi$, and for $|a|<1$ let $\mathrm{ph}_a(z)=\frac12+\arg(1-az)/\pi$. Let $a_\varepsilon=(1-\varepsilon^2)+\varepsilon i$. For every $z$ on the unit circle,
--   $$
--   \mathrm{ph}_{a_\varepsilon}(z)\to\mathrm{ph}(z)\qquad(\varepsilon\to0^+).
--   $$
--
--   The approach from the upper side of the cut makes the limit $0$ also at $z=1$, matching $\mathrm{ph}(1)=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/ScalarPhase.lean#L151-L188

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

theorem OAI.KervaireScalarPhase.tendsto_smoothPhase_cut {z : ℂ} (hz : ‖z‖ = 1) :
    Tendsto (fun ε : ℝ => smoothPhase (cutApproach ε) z)
      (𝓝[>] 0) (𝓝 (phase z)) := by sorry
