-- Prove2me | Theorems.Thm_OAI_KervaireSpectral_tendsto_calculus
-- name    : OAI.KervaireSpectral.tendsto_calculus
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:37:31.985342+00:00
-- url     : https://prove2.me/theorems/2e8c8f2f-6aa1-4030-a4c8-95d3145ca326
-- title:
--   Bounded pointwise convergence to a continuous function
-- statement:
--   Let $U$ be a normal operator on a complex Hilbert space $H$, with continuous functional calculus $f\mapsto f(U)$ on its spectrum. Let $f_n,g$ be continuous on the spectrum with $|f_n|\le C$ and $f_n\to g$ pointwise. Then for every vector $\xi$,
--   $$
--   f_n(U)\xi\to g(U)\xi .
--   $$
--
--   This is the bounded convergence theorem for the continuous functional calculus.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/SpectralMeasures.lean#L328-L357

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures

open OAI OAI.KervaireSpectral
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem OAI.KervaireSpectral.tendsto_calculus (U : Operator H) [hU : IsStarNormal U]
    (f : ℕ → C(spectrum ℂ U, ℂ)) (g : C(spectrum ℂ U, ℂ))
    (C : ℝ) (_hC : 0 ≤ C) (hb : ∀ n z, ‖f n z‖ ≤ C)
    (ht : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (g z))) (ξ : H) :
    Tendsto (fun n => cfcHom hU (f n) ξ) atTop (𝓝 (cfcHom hU g ξ)) := by sorry
