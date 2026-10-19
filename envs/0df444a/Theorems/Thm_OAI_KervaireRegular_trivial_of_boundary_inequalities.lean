-- Prove2me | Theorems.Thm_OAI_KervaireRegular_trivial_of_boundary_inequalities
-- name    : OAI.KervaireRegular.trivial_of_boundary_inequalities
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:19:30.222774+00:00
-- url     : https://prove2.me/theorems/54e61894-cb55-4f89-b27f-d52670860b1e
-- title:
--   Boundary phase inequalities force a trivial coefficient
-- statement:
--   Let $A$ be a group, $Z$ a finite nonempty set with $N=|Z|-1$, and $c:Z\to A$. Let $\mathrm{gph}_z(a)$ be the phase of $zL(a)$ at $\delta_1$ in $\ell^2(A)$. Fix $z_0\in Z$ and suppose that for every $\varepsilon\in(0,1)$,
--   $$
--   \mathrm{gph}_{e^{2\pi iN\varepsilon}}\bigl(c(z_0)\bigr)+N(1-\varepsilon)\le N .
--   $$
--   Then $c(z_0)=1$.
--
--   This is the final step of the rigidity argument: phase inequalities at the boundary of a diagram force the missing corner to be trivial.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/MixingOperators.lean#L269-L302

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
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators

open OAI OAI.KervaireRegular
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open KervaireSpectral KervaireTraceCalculus MeasureTheory
variable {A : Type*} [Group A]

theorem OAI.KervaireRegular.trivial_of_boundary_inequalities {Z : Type*} [Fintype Z] [Nonempty Z]
    (z₀ : Z) (c : Z → A)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 →
      groupPhase (scalarRotation (((Fintype.card Z : ℝ)-1)*ε)) (scalarRotation_unitary _) (c z₀)
        + ((Fintype.card Z : ℝ)-1)*(1-ε) ≤ (Fintype.card Z : ℝ)-1) :
    c z₀ = 1 := by sorry
