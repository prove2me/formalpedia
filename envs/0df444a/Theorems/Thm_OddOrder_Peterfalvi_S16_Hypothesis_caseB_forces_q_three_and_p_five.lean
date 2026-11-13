-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_Hypothesis_caseB_forces_q_three_and_p_five
-- name    : OddOrder.Peterfalvi.S16.Hypothesis.caseB_forces_q_three_and_p_five
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:37:06.613421+00:00
-- url     : https://prove2.me/theorems/afb727e8-51d5-4bd6-826f-bd12f0bdac1f
-- title:
--   Peterfalvi (14.14.b)/(14.15): arithmetic core forces $q=3$ and $p=5$ in case (b)
-- statement:
--   Let `hyp` be a Peterfalvi §14 configuration with parameters $p=$ `hyp.base.p`, $q=$ `hyp.base.q`, $v=$ `hyp.base.v` (and no hypothesis on $G$ beyond the group). Assume
--
--   - $v = (q^p-1)/(q-1)$ (natural-number division);
--   - $\dfrac{v-1}{pq} \le pq-1$ in $\mathbb{Q}$ (with $v-1$ and $pq-1$ computed in $\mathbb{N}$, then cast).
--
--   Then
--   $$q = 3\quad\text{and}\quad p = 5 .$$
--
--   The hypothesis on $(v-1)/(pq)$ is the $(\beta_L,\psi)$-pairing bound of (14.14.b); combined with the cyclotomic value of $v$ it pins down the exceptional primes in the proof via the exponential comparison (14.8.a), which uses the primality and ordering of $p,q$ carried by the configuration `hyp`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/ComparingLM.lean#L262-L349

import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_BetaVanishing
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace Hypothesis

theorem caseB_forces_q_three_and_p_five (hyp : Hypothesis (G := G))
    (hv : hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
    (hbound : ((hyp.base.v - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) ≤
      ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ)) :
    hyp.base.q = 3 ∧ hyp.base.p = 5 := by sorry

end Hypothesis

end OddOrder.Peterfalvi.S16
