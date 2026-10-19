-- Prove2me | Theorems.Thm_OAI_KervaireRibbon_suppress_sign
-- name    : OAI.KervaireRibbon.suppress_sign
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:04:00.708325+00:00
-- url     : https://prove2.me/theorems/aa8ae0c5-758e-4409-8400-f4e0cad43fbb
-- title:
--   Capped signs are antisymmetric under suppression
-- statement:
--   For an involution $\theta$ and darts $x,y$, the suppression is $\mathrm{supp}(\theta,x,y)=(x\ y)\,(y\ \theta x)\,\theta\,(y\ \theta x)$; it fixes $x$ and $y$ and reroutes the edges at $x$ and $y$ into one edge joining $\theta x$ and $\theta y$. Let $\theta$ be an involution, $t$ signs with $t(\theta d)=-t(d)$, and $x\ne y$ with $\theta x\ne x$, $\theta y\ne y$ and $t(y)=-t(x)$. Let $t'$ be the capped signs, equal to $0$ at $x,y$ and to $t$ elsewhere. Then for every $d$,
--   $$
--   t'\bigl(\mathrm{supp}(\theta,x,y)\,d\bigr)=-t'(d).
--   $$
--
--   So capping a cancelling pair keeps edges joining darts of opposite signs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/Capping.lean#L54-L79

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
import Definitions.Def_OAI_GroupTheory_Kervaire_Splicing
import Definitions.Def_OAI_GroupTheory_Kervaire_Capping

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]

omit [Fintype D] in
theorem OAI.KervaireRibbon.suppress_sign (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (t : D → ℤ) (ht : ∀ d, t (θ d) = -t d)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hy : θ y ≠ y) (hpair : t y = -t x) :
    ∀ d, capSign t x y (suppress θ x y d) = - capSign t x y d := by sorry
