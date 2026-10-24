-- Prove2me | Theorems.Thm_K24_Global_section_neumann_transfer
-- name    : K24.Global.section_neumann_transfer
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T18:24:12.378873+00:00
-- url     : https://prove2.me/theorems/387600f0-1631-4bcd-885e-e2ad40b1ad4d
-- title:
--   K24 exact section Neumann transfer with inverse bound and dual gap
-- statement:
--   Let $S\subseteq X$ and $T\subseteq Y$ be real linear section spaces with the published concrete Banach norm and completeness laws, expressed by finite extended norms $n_X,n_Y$ on those sets. Suppose $A:S\to T$ is a bounded linear bijection and, for a finite $C\ge0$,
--   $$n_X(u)\le C\,n_Y(Au)\qquad(u\in S).$$
--   Let $B:S\to T$ be bounded linear, using the actual restrictions of the given maps on $X$. Define the difference norm by the infimum of all valid bounds:
--   $$q=\inf\{D\in[0,\infty]:n_Y(Bu-Au)\le D\,n_X(u)\text{ for all }u\in S\}.$$
--   If $Cq<1/2$, then $B$ is a bounded linear bijection and
--   $$n_X(u)\le 2C\,n_Y(Bu)\qquad(u\in S).$$
--   Moreover every bounded linear functional $\phi$ on $T$ satisfies the actual pullback dual estimate
--   $$\|\phi\|\le 2C\,\|\phi\circ B\|,$$
--   where these norms use the same infimum definition.
--
--   No normed-space structure on the ambient modules $X,Y$ is assumed: the proof constructs the complete normed structures on the actual section subsets from the stated laws. The case $C=0$ is included. This supplies the functional-analytic step for the tensor, natural vector, shifted vector and Sobolev inverse-transfer clauses of full K24. Their geometric section-space laws, mapping properties and estimates still require separate proofs; the complete parent remains https://prove2.me/theorems/aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — §4, equations (4.1)–(4.3), plus the actual section-norm and Banach-dual realization used by FullK24Statement.

import Definitions.Def_K24GlobalAnalysis
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal

namespace K24.Global

theorem section_neumann_transfer
    {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    {S : Set X} {T : Set Y} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) (hT : SectionBanachSpace T ny)
    {A B : X → Y} {C : ℝ≥0}
    (hA : SectionIsomorphism S T nx ny A)
    (hInv : SectionInverseBound S nx ny A C)
    (hBT : Set.MapsTo B S T) (hBL : SectionLinearOn S B)
    (hBB : SectionBoundedOn S nx ny B)
    (hsmall : (C : ℝ≥0∞) * sectionOperatorENorm S nx ny (fun u => B u - A u) < 1 / 2) :
    SectionIsomorphism S T nx ny B ∧ SectionInverseBound S nx ny B (2 * C) ∧
      SectionDualGap S T nx ny B (2 * C) := by
  sorry

end K24.Global
