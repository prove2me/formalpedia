-- Prove2me | Theorems.Thm_OAI_KervaireRibbon_planar_cap
-- name    : OAI.KervaireRibbon.planar_cap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:55:34.246357+00:00
-- url     : https://prove2.me/theorems/49defb19-c7be-40ab-9ba9-f2fd82cbea43
-- title:
--   Capping a cancelling pair preserves planarity
-- statement:
--   For a permutation $\sigma$ of $D$ and a dart $x$, $\mathrm{erase}(\sigma,x)=(x\ \sigma x)\,\sigma$ removes $x$ from its cycle and makes it a fixed point. Suppressing the vertex $\{x,y\}$ in an involution $\theta$ is $\mathrm{supp}(\theta,x,y)=(x\ y)\,(y\ \theta x)\,\theta\,(y\ \theta x)$. Let $(\sigma,\theta)$ be planar with $\theta$ an involution, and $x\ne y$ with $\sigma x=y$, $\sigma y\ne x$, $\theta x\ne x$ and $\theta y\ne y$. Then
--   $$
--   \bigl(\mathrm{erase}(\mathrm{erase}(\sigma,x),y),\ \mathrm{supp}(\theta,x,y)\bigr)\ \text{is planar}.
--   $$
--
--   This is the step of the capping induction that removes a cancelling pair of consecutive darts while staying in genus zero.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/RelatorRigidity.lean#L87-L108

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
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal
import Definitions.Def_OAI_GroupTheory_Kervaire_BoundaryFlow
import Definitions.Def_OAI_GroupTheory_Kervaire_RelatorRigidity

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]

theorem OAI.KervaireRibbon.planar_cap (σ θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hs : σ x = y) (hz : σ y ≠ x)
    (hx : θ x ≠ x) (hy : θ y ≠ y) (hp : planar σ θ) :
    planar (erase (erase σ x) y) (suppress θ x y) := by sorry
