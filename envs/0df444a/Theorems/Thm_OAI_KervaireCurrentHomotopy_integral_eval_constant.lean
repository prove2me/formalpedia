-- Prove2me | Theorems.Thm_OAI_KervaireCurrentHomotopy_integral_eval_constant
-- name    : OAI.KervaireCurrentHomotopy.integral_eval_constant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:24:30.664912+00:00
-- url     : https://prove2.me/theorems/31713c1d-c358-482b-b75c-fce4644e9b64
-- title:
--   Integrated closed forms are constant along a flow
-- statement:
--   Let $S$ be a compact space with a finite measure, $e:S\to E$ continuous, and $\omega$ a smooth $(n+1)$-form on $\mathbb R\times E$. Let $V_0,\dots,V_{n+1}$ be smooth vector fields with $V_0=(1,0)$ the time direction, satisfying three conditions. First, $\int dg(V_i)=0$ over $S$ for $i\ne0$ and every smooth $g$, so the fields are divergence-free. Second, $\omega$ vanishes on the Lie brackets $[V_i,V_j]$ completed by the remaining fields. Third, $d\omega=0$ on the fields. Then
--   $$
--   t\mapsto\int_S\omega_{(t,e(x))}\bigl(V_1,\dots,V_{n+1}\bigr)\,d\mu(x)
--   $$
--   is constant.
--
--   This is the homotopy invariance of currents integrated over an invariant family.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/HaarCurrents.lean#L126-L185

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
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents

open OAI
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
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open KervaireHaarFlow VectorField ContinuousAlternatingMap
open scoped ContDiff
variable {S E : Type*} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S]
  [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ]

theorem OAI.KervaireCurrentHomotopy.integral_eval_constant {n : ℕ} {e : S → E} (he : Continuous e)
    {form : (ℝ × E) → (ℝ × E) [⋀^Fin (n+1)]→L[ℝ] ℝ}
    (hf : ContDiff ℝ ∞ form)
    {V : Fin (n+2) → (ℝ × E) → (ℝ × E)} (hV : ∀ i, ContDiff ℝ ∞ (V i))
    (hVzero : ∀ p, V 0 p = (1, 0))
    (hdiv : ∀ (t : ℝ) (i : Fin (n+2)), i ≠ 0 → ∀ (g : (ℝ × E) → ℝ),
      ContDiff ℝ ∞ g →
      (∫ x, fderiv ℝ g (t,e x) (V i (t,e x)) ∂μ) = 0)
    (hbracket : ∀ (t : ℝ) (x : S) (i j : Fin (n+1)), i ≤ j →
      form (t,e x) (Matrix.vecCons (lieBracket ℝ (V i.castSucc) (V j.succ) (t,e x))
        (j.removeNth (i.castSucc.removeNth (fun l ↦ V l (t,e x))))) = 0)
    (hclosed : ∀ (t : ℝ) (x : S),
      extDeriv form (t,e x) (fun l ↦ V l (t,e x)) = 0) (t₀ t₁ : ℝ) :
    (∫ x, form (t₀,e x) ((0 : Fin (n+2)).removeNth (fun l ↦ V l (t₀,e x))) ∂μ) =
    (∫ x, form (t₁,e x) ((0 : Fin (n+2)).removeNth (fun l ↦ V l (t₁,e x))) ∂μ) := by sorry
