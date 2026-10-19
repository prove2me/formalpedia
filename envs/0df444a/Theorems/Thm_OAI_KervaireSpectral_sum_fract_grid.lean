-- Prove2me | Theorems.Thm_OAI_KervaireSpectral_sum_fract_grid
-- name    : OAI.KervaireSpectral.sum_fract_grid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:55:59.838483+00:00
-- url     : https://prove2.me/theorems/c16001ad-6391-4cd5-82ca-576e745cd5ce
-- title:
--   Summing fractional parts over a grid
-- statement:
--   For an integer $d\ge1$ and $0\le x<1$,
--   $$
--   \sum_{j=0}^{d-1}\Bigl\{x+\frac jd\Bigr\}=\frac{d-1}2+\{dx\},
--   $$
--   where $\{\cdot\}$ denotes the fractional part.
--
--   This is the fractional-part form of Hermite's identity $\sum_j\lfloor x+j/d\rfloor=\lfloor dx\rfloor$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PhaseGrids.lean#L30-L72

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

open OAI OAI.KervaireSpectral
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder

theorem OAI.KervaireSpectral.sum_fract_grid (d : ℕ) (hd : 0 < d) (x : ℝ) (hx : 0 ≤ x ∧ x < 1) :
    (∑ j : Fin d, Int.fract (x + (j.val : ℝ) / d)) =
      ((d : ℝ)-1)/2 + Int.fract ((d : ℝ)*x) := by sorry
