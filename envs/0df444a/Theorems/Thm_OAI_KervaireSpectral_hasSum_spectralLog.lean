-- Prove2me | Theorems.Thm_OAI_KervaireSpectral_hasSum_spectralLog
-- name    : OAI.KervaireSpectral.hasSum_spectralLog
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:48:18.502207+00:00
-- url     : https://prove2.me/theorems/579218c8-17d9-43b5-b4ff-aacb549683c1
-- title:
--   The Mercator series on the unitary spectrum
-- statement:
--   Let $U$ be a unitary on a Hilbert space and $|a|<1$. On the spectrum of $U$, which lies in the unit circle, the functions $\frac{a^{n+1}}{n+1}z^{n+1}$ sum in the supremum norm:
--   $$
--   \sum_{n\ge0}\frac{a^{n+1}z^{n+1}}{n+1}=-\log(1-az).
--   $$
--
--   So the calculus of the spectral logarithm is the norm-convergent operator series $\sum_n\frac{a^{n+1}}{n+1}U^{n+1}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/SpectralApproximation.lean#L32-L71

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
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation

open OAI OAI.KervaireSpectral
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem OAI.KervaireSpectral.hasSum_spectralLog (U : Operator H) (hU : U ∈ unitary (Operator H))
    {a : ℂ} (ha : ‖a‖ < 1) :
    HasSum (fun n : ℕ => (a ^ (n+1) / (n+1)) •
      ((ContinuousMap.id ℂ).restrict (spectrum ℂ U)) ^ (n+1)) (spectralLog U hU a ha) := by sorry
