-- Prove2me | Theorems.Thm_OAI_CriticalZ3_LatticeGraph_bad_success_mass
-- name    : OAI.CriticalZ3.LatticeGraph.bad_success_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:31:33.846982+00:00
-- url     : https://prove2.me/theorems/9eabebd7-1916-4896-ae42-e46f14c7f24b
-- title:
--   Bad successful trials have small mass
-- statement:
--   Work with bond or site percolation on a finite lattice graph $G\subseteq\mathbb Z^3$ under a product law $\mathbb P_p$; "$o\leadsto T$" means that $o$ is connected in $G$ to a vertex of $T$. Boxes $C$ have bits (bonds or sites), exterior vertices adjacent to them, and entry bits. For a box $C$ wide enough for radius $r$ and an exterior vertex $y$, the seed cube of $y$ is the cube of radius $r$ at its relay centre inside $C$, and the success bits of $y$ are the seed cube's bits plus, in the bond model, the entry bond; $\mathrm{seedCard}$ and $\mathrm{successCard}$ are their numbers. Assume all bits of $C+1$ have parameter $q$, $F$ is determined by the bits of $C$, and
--   $$
--   \mathbb P_p(\text{seed bits open}\cap F)\le q^{\mathrm{seedCard}}\gamma/\tau .
--   $$
--   Then the same holds with the success bits: $\mathbb P_p(\text{success bits open}\cap F)\le q^{\mathrm{successCard}}\gamma/\tau$.
--
--   This accounts for the extra entry bond of the bond model.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/SeedQuality.lean#L164-L204

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
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality

open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem OAI.CriticalZ3.LatticeGraph.bad_success_mass (p : m.Bit → Set.Icc (0 : ℝ) 1) (q : Set.Icc (0 : ℝ) 1)
    (C : Box) (r : ℕ) (hw : ∀ i, C.lower i+r ≤ C.upper i-r)
    {y : Vertex} (hy : C.Exterior y)
    (hp : ∀ e ∈ (C.expand 1).bits m, p e = q)
    (F : Set m.Config) (hF : ProductCylinder.DeterminedBy (F := Prop) (C.bits m) (fun ω => ω ∈ F))
    {γ τ : ℝ} (hqual : (ProductCylinder.law p).real
      (allValue ((C.seedBox r y).bits m) true ∩ F) ≤ (q : ℝ)^Box.seedCard m r*γ/τ) :
    (ProductCylinder.law p).real (allValue (C.successBits r m y) true ∩ F) ≤
      (q : ℝ)^Box.successCard m r*γ/τ := by sorry
