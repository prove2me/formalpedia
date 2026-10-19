-- Prove2me | Theorems.Thm_OAI_KervaireTraceCalculus_hasDerivAt_smoothTrace_path
-- name    : OAI.KervaireTraceCalculus.hasDerivAt_smoothTrace_path
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:47:47.107068+00:00
-- url     : https://prove2.me/theorems/42b2bc38-0903-49fb-8317-8f701937dd92
-- title:
--   Derivative of the smooth traced phase along a phase path
-- statement:
--   Let $\tau$ be a tracial continuous functional on a nontrivial C*-algebra, $U$ unitary, $B\ge0$ and $|a|<1$. Let $W_t=Ue^{2\pi itB}$, and let the smooth traced phase be $\frac{\mathrm{Re}\,\tau(1)}2-\frac1\pi\mathrm{Im}\,\tau(-\log(1-aW))$. Then $t\mapsto\mathrm{smooth}_a(W_t)$ has derivative
--   $$
--   -2\,\mathrm{Re}\,\tau\Bigl(\sum_{n\ge0}(aW_t)^{n+1}\,B\Bigr).
--   $$
--
--   Combined with the trace bound, this shows that the regularized phase grows at most like $\mathrm{Re}\,\tau(B)$ per unit time.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/TraceCalculus.lean#L287-L314

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

open OAI OAI.KervaireTraceCalculus
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped Topology
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedRing E]
  [NormedAlgebra 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A]

theorem OAI.KervaireTraceCalculus.hasDerivAt_smoothTrace_path (τ : A →L[ℂ] ℂ)
    (ht : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    {U B : A} (hU : U ∈ unitary A) (hB : 0 ≤ B)
    {a : ℂ} (ha : ‖a‖ < 1) (t : ℝ) :
    HasDerivAt (fun t : ℝ => smoothTrace τ a
      (U * NormedSpace.exp (t • phaseVelocity B)))
      (-2 * (τ ((∑' n : ℕ, (a • (U * NormedSpace.exp
        (t • phaseVelocity B))) ^ (n+1)) * B)).re) t := by sorry
