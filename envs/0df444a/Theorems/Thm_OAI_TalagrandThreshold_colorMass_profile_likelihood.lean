-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_colorMass_profile_likelihood
-- name    : OAI.TalagrandThreshold.colorMass_profile_likelihood
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T13:10:28.699406+00:00
-- url     : https://prove2.me/theorems/a1291f6e-b115-4177-a2d7-4addaa367eea
-- title:
--   Likelihood of an original coloring relative to its earlier move
-- statement:
--   Fix $s\in\mathbb{N}$. Colors are $0,\dots,s$ and a coloring of a finite set $X$ is a map $a:X\to\{0,\dots,s\}$. For colorings $a,z$ with $z\le a$ pointwise, the changed set is $\{x:z(x)<a(x)\}$, the moved row $i$ is $\{x:z(x)=i<a(x)\}$, and the profile $n_{a,z}(i,h)$ counts points with final color $i<s$ and original color $h>i$. Write $r_i(n)=\sum_hn(i,h)$ and $|n|=\sum_ir_i(n)$. For $p>0$ with $p\Sigma_s\le\frac12$, where $\Sigma_s=\sum_{i<s}256^{\,i+1}$, colors have probabilities $\pi_c=256^{c+1}p$ for $c<s$ and $\pi_s=1-p\Sigma_s$, and a coloring $a$ has mass $\prod_{x}\pi_{a(x)}$. For colorings $z\le a$,
--   $$
--   p^{|n_{a,z}|}\,\mathrm{mass}(a)=\mathrm{mass}(z)\prod_{i<s}\Bigl(\frac{p}{\pi_i}\Bigr)^{r_i(n_{a,z})}\prod_h\pi_h^{\,n_{a,z}(i,h)} .
--   $$
--
--   The weight $p^{|\text{changes}|}\mathrm{mass}(a)$ of a bad coloring, seen from its move $z$, factors into the mass of $z$ and a profile-dependent ratio.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/ProbabilityLikelihood.lean#L87-L140

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_TalagrandExpectationThreshold
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMasses
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingExpectation
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityColors
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ScaleBounds
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorTruncationDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorFeasibility
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncoding
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWords
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWordsTransport
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingRows
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorProfile
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingBound
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDelay
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCommonWitness

open OAI OAI.TalagrandThreshold
open scoped BigOperators
open Selector
variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

omit [DecidableEq α] in
theorem OAI.TalagrandThreshold.colorMass_profile_likelihood (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (a z : Coloring α s) (haz : Selector.Earlier a z) :
    p ^ Selector.profileSize (Selector.profile a z) * colorMass p s a =
      colorMass p s z * ∏ i : Fin s,
        ((p / colorProb p s i.castSucc) ^ Selector.rowCount (Selector.profile a z) i *
          ∏ h : Color s, (colorProb p s h) ^ Selector.profile a z i h) := by sorry
