-- Prove2me | Theorems.Thm_OAI_KervaireRibbon_cap_vertex
-- name    : OAI.KervaireRibbon.cap_vertex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:54:55.94133+00:00
-- url     : https://prove2.me/theorems/ba6784fb-138a-402f-92f9-704e4e47a2c9
-- title:
--   Erasing two consecutive darts as a vertex split
-- statement:
--   For a permutation $\sigma$ of $D$ and a dart $x$, $\mathrm{erase}(\sigma,x)=(x\ \sigma x)\,\sigma$ removes $x$ from its cycle and makes it a fixed point. Let $x\ne y$ be darts with $\sigma x=y$ and $\sigma y\ne x$. Then
--   $$
--   \mathrm{erase}(\mathrm{erase}(\sigma,x),y)=(x\ y)\,(x\ \sigma y)\,\sigma .
--   $$
--
--   So capping two consecutive darts of a vertex is a vertex split, which detaches the arc $x\to y$ as a $2$-cycle, followed by a split of that $2$-cycle into two fixed points.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/RelatorRigidity.lean#L49-L71

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

omit [Fintype D] in
theorem OAI.KervaireRibbon.cap_vertex (σ : Perm D) {x y : D} (hxy : x ≠ y) (hs : σ x = y) (hz : σ y ≠ x) :
    erase (erase σ x) y = swap x y * (swap x (σ y) * σ) := by sorry
