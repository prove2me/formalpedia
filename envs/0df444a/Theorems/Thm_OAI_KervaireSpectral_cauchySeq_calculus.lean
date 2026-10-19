-- Prove2me | Theorems.Thm_OAI_KervaireSpectral_cauchySeq_calculus
-- name    : OAI.KervaireSpectral.cauchySeq_calculus
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:34:55.83268+00:00
-- url     : https://prove2.me/theorems/37f86143-72c8-499d-ba96-b07e9429e72d
-- title:
--   Bounded pointwise convergence gives strongly Cauchy calculus
-- statement:
--   Let $U$ be a normal operator on a complex Hilbert space $H$, with continuous functional calculus $f\mapsto f(U)$ on its spectrum. Let $f_n$ be continuous functions on the spectrum with $|f_n|\le C$, converging pointwise to a function $g$. Then for every vector $\xi$ the sequence
--   $$
--   f_n(U)\xi
--   $$
--   is Cauchy in $H$.
--
--   No continuity of the pointwise limit $g$ is required.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/SpectralMeasures.lean#L169-L206

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

theorem OAI.KervaireSpectral.cauchySeq_calculus (U : Operator H) [hU : IsStarNormal U]
    (f : ℕ → C(spectrum ℂ U, ℂ)) (g : spectrum ℂ U → ℂ)
    (C : ℝ) (_hC : 0 ≤ C) (hb : ∀ n z, ‖f n z‖ ≤ C)
    (ht : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (g z))) (ξ : H) :
    CauchySeq (fun n => cfcHom hU (f n) ξ) := by sorry
