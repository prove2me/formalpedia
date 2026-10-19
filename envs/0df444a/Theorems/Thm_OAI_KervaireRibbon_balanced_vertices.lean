-- Prove2me | Theorems.Thm_OAI_KervaireRibbon_balanced_vertices
-- name    : OAI.KervaireRibbon.balanced_vertices
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:56:23.650713+00:00
-- url     : https://prove2.me/theorems/6fe392b3-e7e4-43dc-9257-1e25819950da
-- title:
--   Balanced polarities pair positive and negative vertices
-- statement:
--   Let $V$ be a finite set and $\varepsilon:V\to\{1,-1\}$ with $\sum_v\varepsilon_v=0$, and let $P=\{v:\varepsilon_v=1\}$. Then there is a bijection
--   $$
--   q:\ P\sqcup P\ \xrightarrow{\ \sim\ }\ V
--   $$
--   with $\varepsilon(q(k))=1$ on the first copy and $\varepsilon(q(k))=-1$ on the second.
--
--   So the relator copies of a balanced diagram are indexed by two copies of one set $K=P$, as the positive and negative disks of the slot model.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/RelatorRigidity.lean#L227-L255

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
variable {V I D : Type*} [Fintype V] [Fintype I] [Fintype D]

theorem OAI.KervaireRibbon.balanced_vertices (ε : V → ℤ) (hε : ∀ v, ε v = 1 ∨ ε v = -1)
    (hzero : (∑ v, ε v) = 0) :
    ∃ q : ({v // ε v = 1} ⊕ {v // ε v = 1}) ≃ V,
      (∀ k, ε (q (Sum.inl k)) = 1) ∧ (∀ k, ε (q (Sum.inr k)) = -1) := by sorry
