-- Prove2me | Theorems.Thm_OAI_InfiniteConditioning_disjoint_blocks_probability
-- name    : OAI.InfiniteConditioning.disjoint_blocks_probability
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:21:43.8092+00:00
-- url     : https://prove2.me/theorems/d084a56e-fdee-455e-b835-f93487ed567b
-- title:
--   Events on disjoint finite blocks are independent
-- statement:
--   Let $\mathbb P_p$ be the product Bernoulli law on $\{0,1\}^E$ (countable $E$), $J\subseteq E$ finite, and for revealed values $\xi$ let $p^{J,\xi}$ be the parameters fixing the bits of $J$ to $\xi$ and keeping $p_e$ elsewhere; the pattern of $\xi$ on $J$ is the cylinder $\{\omega:\omega|_J=\xi|_J\}$. If $A_i$ is determined by the bits in $J_i$ and the blocks $J_i$ are pairwise disjoint, then for every finite set $s$ of indices,
--   $$
--   \mathbb P_p\Bigl(\bigcap_{i\in s}A_i\Bigr)=\prod_{i\in s}\mathbb P_p(A_i).
--   $$
--
--   It is used for the independence of seed trials.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Conditioning.lean#L214-L245

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning

open OAI OAI.InfiniteConditioning
universe uF
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical
variable {E I : Type}

theorem OAI.InfiniteConditioning.disjoint_blocks_probability (p : E → Set.Icc (0 : ℝ) 1)
    (J : I → Finset E) (hJ : Pairwise (fun i j => Disjoint (J i) (J j)))
    (A : I → Set (E → Bool))
    (hA : ∀ i, ProductCylinder.DeterminedBy (F := Prop) (J i) (fun ω => ω ∈ A i))
    (s : Finset I) :
    (ProductCylinder.law p).real {ω | ∀ i ∈ s, ω ∈ A i} =
      ∏ i ∈ s, (ProductCylinder.law p).real (A i) := by sorry
