-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_MHypothesis_line83_le_displayed_upper
-- name    : OddOrder.Peterfalvi.S16.MHypothesis.line83_le_displayed_upper
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:32:37.940635+00:00
-- url     : https://prove2.me/theorems/e89b74ab-2afe-45b7-9975-1ae5563846b4
-- title:
--   Peterfalvi (14.11.4): the line-83 bound is at most the displayed upper bound
-- statement:
--   Let $G$ be a finite minimal simple odd-order group with no maximal subgroup of type V (`hnoV`), `hyp` a Peterfalvi §14 configuration with parameters $p,q,u,v$, and `Mdata : MHypothesis hyp` the data for a type-I maximal subgroup $M$ (with complement index $e$ = `Mdata.e`). Assume $e = pq$. Then, in $\mathbb{R}$,
--   $$\frac{|A(M)|}{|M|} + \frac{1}{|G|}\Bigl(|G_0| - \bigl|\{g\in G : g\in \texttt{Mdata.G0}\}\bigr|\Bigr) \;\le\; 1-\frac1p-\frac1q+\frac{2}{pq}+\frac1{uq}+\frac1{vp},$$
--   where $|A(M)|$ is `Nat.card (typeIA M Mdata.typeIHyp.typeI)`, $|G_0|$ is the cardinality of the underlying $G_0$ of `Mdata.toFamilyHypothesis71`, and the subtracted count is the cardinality of the finite set `{g | g ∈ Mdata.G0}`.
--
--   This is the upper-bound step of the section 8 TI counting in (14.11.4): it brings the line-83 bound up to the displayed bound, using $|A(M)|/|M|=(k-1)/(kpq)$, orbit measures of the Frobenius pieces $W,P,Q$, and the TI properties.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupM.lean#L922-L1061

import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ConjugationFieldModel
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupMCore
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupM

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in

theorem MHypothesis.line83_le_displayed_upper [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) (hepq : Mdata.e = hyp.base.p * hyp.base.q) :
    (Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) : ℝ)
        / (Nat.card ↥Mdata.M : ℝ)
      + (Nat.card G : ℝ)⁻¹ * ((Nat.card (Mdata.toFamilyHypothesis71).G0 : ℝ)
        - ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ))
      ≤ 1 - (1 : ℝ) / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ)
        + 2 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ)
        + 1 / ((hyp.base.u * hyp.base.q : ℕ) : ℝ)
        + 1 / ((hyp.base.v * hyp.base.p : ℕ) : ℝ) := by sorry

end OddOrder.Peterfalvi.S16
