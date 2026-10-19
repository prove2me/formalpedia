-- Prove2me | Theorems.Thm_OAI_KervaireRibbon_disk_sameCycle
-- name    : OAI.KervaireRibbon.disk_sameCycle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:57:43.150779+00:00
-- url     : https://prove2.me/theorems/a81e63ad-6895-4e09-89b4-2aa6718295a1
-- title:
--   Each relator disk is a single vertex
-- statement:
--   Let $\rho$ be a cyclic permutation of $I$. A disk atlas for a permutation $\sigma$ of darts $D$ is an injection $(v,i)\mapsto\mathrm{disk}(v,i)$ of $V\times I$ into $D$ with polarities $\varepsilon_v=\pm1$, such that $\sigma$ moves $\mathrm{disk}(v,i)$ to $\mathrm{disk}(v,\rho^{\varepsilon_v}i)$ and dart signs are $\varepsilon_vs_i$. Then for every $v$ and $i,j\in I$,
--   $$
--   \mathrm{disk}(v,i)\ \text{and}\ \mathrm{disk}(v,j)\ \text{lie in the same cycle of}\ \sigma .
--   $$
--
--   So each copy of the relator forms one vertex of the ribbon graph.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/RelatorRigidity.lean#L356-L384

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
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

omit [Fintype V] [Fintype D] [DecidableEq D] [Group A] in
theorem OAI.KervaireRibbon.disk_sameCycle (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j)
    (a : I → A) (s : I → ℤ) (σ : Perm D) (t : D → ℤ)
    (b : DiskAtlas (V := V) ρ a s σ t) (v : V) (i j : I) :
    σ.SameCycle (b.disk (v,i)) (b.disk (v,j)) := by sorry
