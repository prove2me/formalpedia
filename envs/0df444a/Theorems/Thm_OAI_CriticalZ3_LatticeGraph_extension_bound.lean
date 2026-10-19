-- Prove2me | Theorems.Thm_OAI_CriticalZ3_LatticeGraph_extension_bound
-- name    : OAI.CriticalZ3.LatticeGraph.extension_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:34:42.92199+00:00
-- url     : https://prove2.me/theorems/2d8f61b4-49a6-49ca-b5b2-2d97b5e05db4
-- title:
--   Reaching a box but not the target is unlikely
-- statement:
--   Work with bond or site percolation on a finite lattice graph $G\subseteq\mathbb Z^3$ under a product law $\mathbb P_p$; "$o\leadsto T$" means that $o$ is connected in $G$ to a vertex of $T$. For a box $C$ wide enough for radius $r$, each exterior vertex $y$ has a seed cube of radius $r$ at its relay centre and success bits (the seed bits, plus the entry bond in the bond model), whose number is $\mathrm{successCard}$; a good relay is a vertex reaching $T$ with conditional probability $>1-\tau$ given the bits of $C$. Let $B$ be a box, $r<R$, $q\le p_0<1$ with $q>0$, $G\supseteq B+R$ with all bits of $B+R$ of parameter $q$, and $o$ outside $B+R$. Suppose every centre $c\in B+R$ has a radius $\ell\ge r$ with $\Lambda_\ell(c)\subseteq G$ and
--   $$
--   \mathbb P_p\bigl(\Lambda_r(c)\leftrightarrow T\ \text{inside}\ \Lambda_\ell(c)\bigr)\ge1-\gamma .
--   $$
--   Then $\mathbb P_p(o\leadsto B,\ o\not\leadsto T)$ is at most
--   $$
--   \frac1{(1-p_0)^{K(8r+5)^3}(R-r)}+\frac4{K\,q^{\mathrm{successCard}}}+\frac{2\gamma}\tau+\tau .
--   $$
--
--   This is the basic step for extending a connection from one region to the next.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Extension.lean#L169-L239

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

theorem OAI.CriticalZ3.LatticeGraph.extension_bound (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ)) {p₀ : ℝ} (hqp : (q : ℝ) ≤ p₀) (hp₀ : p₀ < 1)
    (B : Box) (r K R : ℕ) (hK : 0 < K) (hrR : r < R)
    (hG : G.ContainsBox (B.expand R)) (o : G.Node) (T : Set Vertex)
    (ho : ¬(B.expand R).Contains o.1)
    (hp : ∀ e ∈ (B.expand R).bits m, p e = q)
    {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 < τ)
    (hreach : ∀ c, (B.expand R).Contains c → ∃ ℓ : ℕ,
      r ≤ ℓ ∧ G.ContainsBox (Box.cube c ℓ) ∧
      1-γ ≤ (ProductCylinder.law p).real (m.SeedReaches c r ℓ T)) :
    (ProductCylinder.law p).real
      {ω | G.Meets m ω o {x | B.Contains x} ∧ ¬G.Meets m ω o T} ≤
      1/((1-p₀)^(K*(8*r+5)^3)*(R-r : ℕ)) +
        4/(K*(q : ℝ)^Box.successCard m r)+2*γ/τ+τ := by sorry
