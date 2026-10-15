-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_entropy_barrier_ge_id
-- name    : OAI.MatchingEntropy.entropy_barrier_ge_id
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:28:49.403973+00:00
-- url     : https://prove2.me/theorems/9911907c-601b-42fc-afd6-d2ad290b7c9a
-- title:
--   The barrier $8(1-e^{-t})$ dominates $t$ on $[0,\log 8]$
-- statement:
--   For every real number $t$ with $0\le t\le\log 8$,
--
--   $$
--   t\;\le\;8\left(1-e^{-t}\right).
--   $$
--
--   Here $\log$ is the natural logarithm. In other words, the concave function $\phi(t)=8(1-e^{-t})$ lies above the identity on the whole interval $[0,\log 8]$.
--
--   The function $\phi$ is the barrier in the entropy defect bound for perfect matchings: for a loopless multigraph on $2m$ vertices and a point $y$ of its perfect matching polytope with marginal entropy $F=H(y)$, the bound reads $F-\mathcal H(y)\le 8m\left(1-e^{-F/m}\right)=m\,\phi(F/m)$, where $\mathcal H(y)\ge0$ is the largest entropy of a probability law on perfect matchings with mean $y$. Taking $t=F/m$, the lemma gives $F\le m\,\phi(F/m)$ whenever $F\le m\log 8$, so in this small-entropy regime the bound holds already because $\mathcal H(y)\ge0$; only the regime $F>m\log 8$ requires the rest of the argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Main.lean#L24-L46

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Polytope
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Face
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Covariance
import Definitions.Def_OAI_Combinatorics_PerfectMatching_MatchingCovariance

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
open Matrix
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem OAI.MatchingEntropy.entropy_barrier_ge_id {t : ℝ} (ht : 0 ≤ t) (h8 : t ≤ Real.log 8) :
    t ≤ 8 * (1-Real.exp (-t)) := by sorry
