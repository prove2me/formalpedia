-- Prove2me | Theorems.Thm_OAI_KervaireRibbon_chain_cap
-- name    : OAI.KervaireRibbon.chain_cap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:01:17.351855+00:00
-- url     : https://prove2.me/theorems/7db70fc3-e223-4cc7-a34a-35d31fc677b8
-- title:
--   Capping removes two darts from a boundary path
-- statement:
--   For a permutation $\sigma$ of $D$ and a dart $x$, $\mathrm{erase}(\sigma,x)=(x\ \sigma x)\,\sigma$ removes $x$ from its cycle. Suppose the list $\mathrm{pre}\,{+\!\!+}\,[d,x,y]\,{+\!\!+}\,\mathrm{post}$ follows $\sigma$, so consecutive entries are $\sigma$-steps. Suppose also $x\ne y$ and no entry of $\mathrm{pre}\,{+\!\!+}\,d::\mathrm{post}$ equals $x$ or $y$. Then $\mathrm{pre}\,{+\!\!+}\,d::\mathrm{post}$ follows
--   $$
--   \mathrm{erase}(\mathrm{erase}(\sigma,x),y).
--   $$
--
--   Capping the consecutive darts $x,y$ deletes them from the boundary path and joins $d$ directly to the dart after $y$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/Circles.lean#L70-L99

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
import Definitions.Def_OAI_GroupTheory_Kervaire_VertexJoin
import Definitions.Def_OAI_GroupTheory_Kervaire_Circles

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [DecidableEq D] [Finite D]

omit [Finite D] in
theorem OAI.KervaireRibbon.chain_cap (σ : Perm D) (pre post : List D) {d x y : D}
    (hc : (pre ++ d::x::y::post).IsChain (fun x y ↦ σ x = y))
    (hxy : x ≠ y) (hno : ∀ z ∈ pre ++ d::post, z ≠ x ∧ z ≠ y) :
    (pre ++ d::post).IsChain (fun a b ↦ erase (erase σ x) y a = b) := by sorry
