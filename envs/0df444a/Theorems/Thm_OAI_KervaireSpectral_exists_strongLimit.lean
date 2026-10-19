-- Prove2me | Theorems.Thm_OAI_KervaireSpectral_exists_strongLimit
-- name    : OAI.KervaireSpectral.exists_strongLimit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:36:31.395663+00:00
-- url     : https://prove2.me/theorems/7b4ed789-fbdb-461f-b55c-60bdacf1ff18
-- title:
--   Strong limits of bounded calculus sequences
-- statement:
--   Let $U$ be a normal operator on a complex Hilbert space $H$, with continuous functional calculus $f\mapsto f(U)$ on its spectrum. Let $f_n$ be continuous functions on the spectrum with $|f_n|\le C$, converging pointwise. Then there is an operator $T$ with $\|T\|\le C$ such that
--   $$
--   f_n(U)\xi\to T\xi\qquad\text{for every }\xi\in H .
--   $$
--
--   This defines bounded Borel-type functions of $U$, such as its phase, as strong limits.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/SpectralMeasures.lean#L208-L228

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

theorem OAI.KervaireSpectral.exists_strongLimit (U : Operator H) [hU : IsStarNormal U]
    (f : ℕ → C(spectrum ℂ U, ℂ)) (g : spectrum ℂ U → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n z, ‖f n z‖ ≤ C)
    (ht : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (g z))) :
    ∃ T : Operator H, (∀ ξ, Tendsto (fun n => cfcHom hU (f n) ξ) atTop (𝓝 (T ξ))) ∧
      ‖T‖ ≤ C := by sorry
