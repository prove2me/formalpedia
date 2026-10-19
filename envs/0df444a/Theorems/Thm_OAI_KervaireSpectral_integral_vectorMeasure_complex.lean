-- Prove2me | Theorems.Thm_OAI_KervaireSpectral_integral_vectorMeasure_complex
-- name    : OAI.KervaireSpectral.integral_vectorMeasure_complex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:38:36.477382+00:00
-- url     : https://prove2.me/theorems/4f1202e4-7e52-4c6f-b21f-430f9d671e63
-- title:
--   Integrals against vector spectral measures
-- statement:
--   Let $U$ be a normal operator on a complex Hilbert space $H$, with continuous functional calculus $f\mapsto f(U)$ on its spectrum. Let $\mu_\xi$ be the spectral measure of a vector $\xi$, the Riesz measure of $f\mapsto\mathrm{Re}\langle\xi,f(U)\xi\rangle$. For every continuous complex function $f$ on the spectrum,
--   $$
--   \int f\,d\mu_\xi=\langle\xi,f(U)\xi\rangle .
--   $$
--
--   Real-valued test functions determine the measure, and the formula extends to complex functions by linearity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/SpectralLogarithm.lean#L140-L161

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

open OAI OAI.KervaireSpectral
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem OAI.KervaireSpectral.integral_vectorMeasure_complex (U : Operator H) [hU : IsStarNormal U] (ξ : H)
    (f : C(spectrum ℂ U, ℂ)) :
    ∫ z, f z ∂vectorMeasure U ξ = vectorCLM ξ (cfcHom hU f) := by sorry
