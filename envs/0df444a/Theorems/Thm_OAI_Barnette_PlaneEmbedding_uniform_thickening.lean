-- Prove2me | Theorems.Thm_OAI_Barnette_PlaneEmbedding_uniform_thickening
-- name    : OAI.Barnette.PlaneEmbedding.uniform_thickening
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:12:48.674239+00:00
-- url     : https://prove2.me/theorems/dbce17c1-5171-4669-9eee-cec903e23a2d
-- title:
--   Finitely many disjoint compact planar sets admit one uniform thickening radius keeping them disjoint
-- statement:
--   For $K\subseteq\mathbb{R}^2$ and $\delta>0$, the open $\delta$-thickening of $K$ is
--   $$K^{\delta}=\Bigl\{x\in\mathbb{R}^2:\ \inf_{k\in K}d(x,k)<\delta\Bigr\},$$
--   the set of points at distance less than $\delta$ from $K$ (empty if $K$ is empty).
--
--   **Theorem.** Let $\iota$ be a finite index set, let $(K_i)_{i\in\iota}$ be compact subsets of $\mathbb{R}^2$, and let $R$ be a binary relation on $\iota$ such that $K_i\cap K_j=\varnothing$ whenever $R(i,j)$ holds. Then there is a single $\delta>0$ such that
--
--   $$
--   R(i,j)\ \Longrightarrow\ K_i^{\delta}\cap K_j^{\delta}=\varnothing\qquad\text{for all } i,j\in\iota .
--   $$
--
--   The relation $R$ records which pairs are required to be separated; pairs not related may intersect. The result supplies a common positive scale below which all prescribed separations of a finite configuration of compact pieces (such as the branches and edge cores of a plane drawing) persist, which is what makes a discretization by grid cells of size smaller than that scale faithful.
--
--   **Formalization Note** The plane is `ℝ × ℝ` with its product metric $d(x,y)=\max(|x_1-y_1|,|x_2-y_2|)$, and the thickening is Mathlib's `Metric.thickening δ K`, defined through the extended infimum distance. The statement lives in the `PlaneEmbedding` namespace but does not involve an embedding.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Traces.lean#L240-L255

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
import Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Matching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ForestMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ThreeCuts
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Gluing
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Traces

open OAI OAI.Barnette OAI.Barnette.PlaneEmbedding
variable {V : Type*} {G : SimpleGraph V} (E : PlaneEmbedding G)

theorem OAI.Barnette.PlaneEmbedding.uniform_thickening {ι : Type*} [Finite ι] (K : ι → Set (ℝ × ℝ))
    (hK : ∀ i, IsCompact (K i)) (R : ι → ι → Prop)
    (hR : ∀ i j, R i j → Disjoint (K i) (K j)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j, R i j →
      Disjoint (Metric.thickening δ (K i)) (Metric.thickening δ (K j)) := by sorry
