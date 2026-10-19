-- Prove2me | Theorems.Thm_OAI_KervaireSpectral_vectorPhase_cfcHom
-- name    : OAI.KervaireSpectral.vectorPhase_cfcHom
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:53:47.145978+00:00
-- url     : https://prove2.me/theorems/002b7722-2fdc-4498-ab87-6f8218eecbed
-- title:
--   Phase of a function of a normal operator
-- statement:
--   Let $U$ be a normal operator, $f$ a continuous function on its spectrum such that $f(U)$ is unitary, and $\xi$ a vector. Then the fractional phase of $f(U)$ at $\xi$ is
--   $$
--   \mathrm{ph}_\xi\bigl(f(U)\bigr)=\int\mathrm{ph}\bigl(f(z)\bigr)\,d\mu_\xi(z),
--   $$
--   integrated against the spectral measure of $U$ at $\xi$.
--
--   This is the naturality of the phase under the continuous functional calculus.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PhaseNaturality.lean#L21-L54

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
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality

open OAI OAI.KervaireSpectral
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem OAI.KervaireSpectral.vectorPhase_cfcHom (U : Operator H) [hN : IsStarNormal U]
    (f : C(spectrum ℂ U, ℂ)) (hf : cfcHom hN f ∈ unitary (Operator H)) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hf
    vectorPhase (cfcHom hN f) ξ = ∫ z, phase (f z) ∂vectorMeasure U ξ := by sorry
