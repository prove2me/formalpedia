-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_norm_cascade_contradiction_of_caseB_outputs_main_size_bounds
-- name    : OddOrder.Peterfalvi.S16.norm_cascade_contradiction_of_caseB_outputs_main_size_bounds
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:27:34.601963+00:00
-- url     : https://prove2.me/theorems/747b768f-1eeb-4160-8d78-3cf0487b269f
-- title:
--   Peterfalvi (14.11.4): the norm cascade yields a contradiction from the case-(b) outputs and size bounds
-- statement:
--   Let `hyp` be a Peterfalvi §14 configuration with parameters $p,q,u,v$, and `Mdata : MHypothesis hyp` with kernel order $k=$ `Mdata.k` and complement index $e=$ `Mdata.e`. Assume
--
--   - (`hT`) there is `data : CaseBForTData hyp` with `data.caseB_formula` and $v = (q^p-1)/(q-1)$;
--   - (`hS`) there is `data : CaseBForSData hyp` with `data.caseB_formula`;
--   - (`hsize`) the three size bounds: $k>2pv$; $\dfrac{k-1}{e} > \dfrac{v-1}{p}$; $\dfrac{v-1}{p}>\dfrac{u-1}{q}$ (the last two in $\mathbb{Q}$, with the subtractions done in $\mathbb{N}$);
--   - (`hbound`) `normCascadeBound hyp k`.
--
--   Then
--   $$\text{False}.$$
--
--   This consumes exactly the output shapes of `caseB_for_T`, `caseB_for_S` and `main_size_bounds` in the norm-cascade contradiction of (14.11.4).
--
--   **Formalization Note.** `normCascadeBound` is a project definition encoding the norm-cascade inequality; the type $G$ has only a `Group` instance here.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean#L480-L497

import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentEtaOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupL
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupMCore

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

theorem norm_cascade_contradiction_of_caseB_outputs_main_size_bounds
    {hyp : Hypothesis (G := G)}
    (hT : ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧ hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
    (hS : ∃ data : CaseBForSData hyp, data.caseB_formula) (Mdata : MHypothesis hyp)
    (hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)))
    (hbound : normCascadeBound hyp Mdata.k) :
    False := by sorry

end OddOrder.Peterfalvi.S16
