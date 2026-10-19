-- Prove2me | Theorems.Thm_OAI_CriticalZ3_LatticeGraph_large_entrants_failure
-- name    : OAI.CriticalZ3.LatticeGraph.large_entrants_failure
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:33:57.643145+00:00
-- url     : https://prove2.me/theorems/d43b49ef-f352-4cfa-bfca-62630505ba61
-- title:
--   Many entrants make reaching a good relay likely
-- statement:
--   Work with bond or site percolation on a finite lattice graph $G\subseteq\mathbb Z^3$ under a product law $\mathbb P_p$; "$o\leadsto T$" means that $o$ is connected in $G$ to a vertex of $T$. For a box $C$ wide enough for radius $r$, each exterior vertex $y$ has a seed cube of radius $r$ at its relay centre and success bits (the seed bits, plus the entry bond in the bond model), whose number is $\mathrm{successCard}$; a good relay is a vertex reaching $T$ with conditional probability $>1-\tau$ given the bits of $C$. Assume all bits of $C+1$ have parameter $q>0$ and that each seed cube is open yet a bad relay with probability at most $q^{\mathrm{seedCard}}\gamma/\tau$. Then
--   $$
--   \mathbb P_p\bigl(|\mathrm{entrants}(C)|\ge K(8r+5)^3\ \text{and}\ o\not\leadsto\text{good relays}\bigr)\le\frac4{K\,q^{\mathrm{successCard}}}+\frac{2\gamma}\tau .
--   $$
--
--   The entrant count is determined by the bits outside $C$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Extension.lean#L112-L150

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
universe uOmega
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem OAI.CriticalZ3.LatticeGraph.large_entrants_failure (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ))
    (C : Box) (r K : ℕ) (hK : 0 < K)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (hC : G.ContainsBox (C.expand 1))
    (o : G.Node) (T : Set Vertex)
    (hp : ∀ e ∈ (C.expand 1).bits m, p e = q) {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 < τ)
    (hqual : ∀ y, C.Exterior y → (ProductCylinder.law p).real
      (allValue ((C.seedBox r y).bits m) true ∩
        {ω | conditionalProbability p (C.bits m)
          {ω | G.Meets m ω (G.relayNode C r hw (hC.mono G (fun _ => C.contains_expand 1)) y) T} ω ≤ 1-τ})
        ≤ (q : ℝ)^Box.seedCard m r*γ/τ) :
    (ProductCylinder.law p).real
      {ω | K*(8*r+5)^3 ≤ (G.entrants m C ω o).card ∧
        ¬G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω)} ≤
        4/(K*(q : ℝ)^Box.successCard m r)+2*γ/τ := by sorry
