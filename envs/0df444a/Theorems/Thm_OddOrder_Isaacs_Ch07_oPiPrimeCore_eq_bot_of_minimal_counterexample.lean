-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_oPiPrimeCore_eq_bot_of_minimal_counterexample
-- name    : OddOrder.Isaacs.Ch07.oPiPrimeCore_eq_bot_of_minimal_counterexample
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:54:48.102212+00:00
-- url     : https://prove2.me/theorems/e4092cfd-ae65-4ac8-8ce7-0ac6b0a95f26
-- title:
--   Isaacs 7.1, Step 3: $O_{p'}(G)=1$ in a minimal counterexample
-- statement:
--   Say that $G$ satisfies the *Thompson local hypothesis at $p$* (`HasThompsonPComplementHypothesis p G`) if for every Sylow $p$-subgroup $P$ of $G$, both $C_G(Z(P))$ and $N_G(J(P))$ have a normal $p$-complement (`HasNormalPComplement`; a normal subgroup that complements every Sylow $p$-subgroup).
--
--   Let $G$ be a finite group, $p$ a prime, and $P$ a Sylow $p$-subgroup. Assume $G$ satisfies the Thompson local hypothesis at $p$; every finite group $H$ (same universe) with $|H|<|G|$ satisfying it has a normal $p$-complement; and $G$ has no normal $p$-complement. Then
--   $$O_{p'}(G)=1 .$$
--
--   This is Step 3 in the proof of Isaacs's Theorem 7.1.
--
--   **Formalization Note.** $O_{p'}(G)$ is `oPiCore {q | q ≠ p} G`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean#L1105-L1219

import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement

namespace OddOrder.Isaacs.Ch07

open scoped Pointwise

variable {G : Type*} [Group G]

section MinimalCounterexampleStepThree

theorem oPiPrimeCore_eq_bot_of_minimal_counterexample.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hHyp : HasThompsonPComplementHypothesis p G)
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    (hG : ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p G) :
    OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥ := by sorry

end MinimalCounterexampleStepThree

end OddOrder.Isaacs.Ch07
