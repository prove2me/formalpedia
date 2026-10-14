-- Prove2me | Theorems.Thm_NLogN_expNegFixP_top
-- name    : NLogN.expNegFixP_top
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-13T12:42:18.579815+00:00
-- url     : https://prove2.me/theorems/5787f3e6-2b51-4547-ab90-65c8c0f372b2
-- title:
--   Cost bound of `expNegFixP`, in terms of `n`, `M`, `zsz X` and `τ = ((-X) / log2Bits M)
-- statement:
--   Cost bound of `expNegFixP`, in terms of `n`, `M`, `zsz X` and `τ = ((-X) / log2Bits M).toNat`. -/ def expNegFixCost (n M zX T : ℕ) : ℕ := 10 ^ 20 * (n + M + zX + T + 20) ^ 5  set_option maxHeartbeats 4000000 in theorem expNegFixP_cost (n M : ℕ) (X : ℤ) (s : IState HS) (L10 L11 L12 : List Item) (h10 : s.G 10 = .int n :: L10) (h11 : s.G 11 = .int M :: L11) (h12 : s.G 12 = .int X :: L12) : expNegFixP.cost s ≤ expNegFixCost n M (zsz X) ((-X) / log2Bits M).toNat := by obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ := expNegFix_bnds n M X have hpi := piCost_le 3 3 M (by norm_num) (by norm_num) have hBdef : expNegB n M (zsz X) (-X / log2Bits M).toNat = expB M (3 * M + 14) + n + M + (-X / log2Bits M).toNat + zsz X + 10 := rfl have hE : 3 * M + 14 ≤ expB M (3 * M + 14) := by simp only [expB]; nlinarith generalize hBc : expNegB n M (zsz X) (-X / log2Bits M).toNat = Bc at * have z0 : zsz (0 : ℤ) = 0 := zsz_zero have z1 : zsz (1 : ℤ) = 1 := zsz_one have g9 : zsz (X + -X / log2Bits M * log2Bits M) ≤ Bc := by omega have g12a : ((((M : ℤ) + -((n : ℤ) + 1)).toNat : ℤ) + ((-X / log2Bits M).toNat : ℤ)).toNat + 1 ≤ Bc + 3 := by omega have g12b : ((((M : ℤ) + -((n : ℤ) + 1)).toNat : ℤ) + ((-X / log2Bits M).toNat : ℤ) + 1).toNat + 1 ≤ Bc + 3 := by omega have g15 : zsz ((expBits M (X + -X / log2Bits M * log2Bits M) 0).1 + 2 ^ ((((M : ℤ) + -((n : ℤ) + 1)).toNat : ℤ) + ((-X / log2Bits M).toNat : ℤ)).toNat) ≤ Bc + 3 := by omega have gone : 1 ≤ Bc + 3 := by omega have hpos2 : ∀ k : ℕ, (0 : ℤ) < 2 ^ k := fun k => by positivity simp (config := {decide := true}) only [expNegFixP, seqL, run_seq, RS.cost] rw [log2P_run' _ (by simp (config := {decide := true}) [IState.IsInt, IState.top, h11]) (by simp (config := {decide := true}) [IState.top, Ex.eval, h11])] rw [expP_run' _ (by simp (config := {decide := true}) [IState.IsInt, IState.top, h11]) (by simp (config := {decide := true}) [IState.top, Ex.eval, h11]) (by simp (config := {decide := true}) [IState.IsInt, IState.top, h11]) (by simp (config := {decide := true}) [IState.IsInt, IState.top, h11])] refine le_trans (add_le_add (pushCost_le _ _ (Bc + 3) ?_) (add_le_add (log2P_cost' _ ?_ ?_) (add_le_add (pushCost_le _ _ (Bc + 3 + 2) ?_) (add_le_add (pushCost_le _ _ (Bc + 3 + 2) ?_) (add_le_add (pushCost_le _ _ (Bc + 3) ?_) (add_le_add (pushCost_le _ _ (Bc + 3) ?_) (add_le_add (pushCost_le _ _ (Bc + 3) ?_) (add_le_add (expP_cost' _ ?_ ?_ ?_ ?_) (add_le_add (pushCost_le _ _ (Bc + 3 + 2) ?_) le_rfl))))))))) ?_ all_goals first | (apply Ex.fdiv_bnd) | (apply Ex.ediv_bnd) | skip all_goals simp (config := {decide := true}) only [Ex.Bnd, Ex.eval, Ex.size, IState.top, IState.IsInt, RS.run_push_G, RS.run_pop_G, IState.upd_G, h10, h11, h12, if_true, if_false, List.tail_cons, Ex.ediv_eval, Ex.max0_eval, tauE, sE, Int.toNat_natCast, Ex.max0_size, Ex.ediv_size, Ex.fdiv_pow2_eval] all_goals (repeat' apply And.intro) all_goals try simp (config := {decide := true}) only [Ex.Bnd, Ex.eval, Ex.size, IState.top, IState.IsInt, RS.run_push_G, RS.run_pop_G, IState.upd_G, h10, h11, h12, if_true, if_false, List.tail_cons, Ex.ediv_eval, Ex.max0_eval, tauE, sE, Int.toNat_natCast, Ex.max0_size, Ex.ediv_size, Ex.fdiv_pow2_eval, exists_eq', List.cons.injEq, true_and, and_true] all_goals (try split_ifs) all_goals (repeat' apply And.intro) all_goals (try simp only [Ex.Bnd]) all_goals first | with_reducible assumption | (apply Nat.le_add_right_of_le; with_reducible assumption) | (apply Nat.le_add_right_of_le; apply Nat.le_add_right_of_le; with_reducible assumption) | (rw [z0]; exact Nat.zero_le _) | (rw [z1]; with_reducible assumption) | (rw [z1]; apply Nat.le_add_right_of_le; with_reducible assumption) | (apply hpos2) | (exact Nat.cast_nonneg _) | skip simp only [Ex.fdiv, Ex.size, z0, expCost, expNegFixCost, show Bc + 3 + 2 = Bc + 5 by omega, show Bc + 3 + 2 + 2 = Bc + 7 by omega] have hS : M + zsz (X + -X / log2Bits M * log2Bits M) + 0 + 20 ≤ 4 * (n + M + zsz X + (-X / log2Bits M).toNat + 20) := by linarith [f9, Nat.zero_le ((-X / log2Bits M).toNat), Nat.zero_le (zsz X), Nat.zero_le n] have hBS : Bc + 7 ≤ 9 * (n + M + zsz X + (-X / log2Bits M).toNat + 20) ^ 2 := by rw [hBdef]; simp only [expB]; nlinarith generalize hSdef : n + M + zsz X + (-X / log2Bits M).toNat + 20 = S at * have hS20 : M + 10 ≤ S := by omega have hZ5 : (Bc + 5) ^ 2 ≤ (Bc + 7) ^ 2 := Nat.pow_le_pow_left (by omega) 2 have hZ : (Bc + 7) ^ 2 ≤ 81 * S ^ 4 := by calc (Bc + 7) ^ 2 ≤ (9 * S ^ 2) ^ 2 := Nat.pow_le_pow_left hBS 2 _ = 81 * S ^ 4 := by ring have hBZ : Bc + 7 ≤ (Bc + 7) ^ 2 := by nlinarith have hE5 : (M + zsz (X + -X / log2Bits M * log2Bits M) + 0 + 20) ^ 5 ≤ 1024 * S ^ 5 := by calc _ ≤ (4 * S) ^ 5 := Nat.pow_le_pow_left hS 5 _ = 1024 * S ^ 5 := by ring have hM3 : (M + 10) ^ 3 ≤ S ^ 3 := Nat.pow_le_pow_left hS20 3 have h35 : S ^ 3 ≤ S ^ 5 := Nat.pow_le_pow_right (by omega) (by omega) have h45 : S ^ 4 ≤ S ^ 5 := Nat.pow_le_pow_right (by omega) (by omega) generalize (M + zsz (X + -X / log2Bits M * log2Bits M) + 0 + 20) ^ 5 = E5 at * generalize (Bc + 7) ^ 2 = Z at * generalize (Bc + 5) ^ 2 = Y at * linarith [f13, f14, g9, f1, f10, f7, f6]  theorem expNegFixP_spec (n M : ℕ) (X : ℤ) (s : IState HS) (L10 L11 L12 : List Item) (h10 : s.G 10 = .int n :: L10) (h11 : s.G 11 = .int M :: L11) (h12 : s.G 12 = .int X :: L12) : expNegFixP.ok s ∧ expNegFixP.run s = s.upd 13 (.int (expNegFix n M X) :: s.G 13) ∧ expNegFixP.cost s ≤ expNegFixCost n M (zsz X) ((-X) / log2Bits M).toNat := ⟨expNegFixP_ok n M X s L10 L11 L12 h10 h11 h12, expNegFixP_run n M X s L10 L11 L12 h10 h11 h12, expNegFixP_cost n M X s L10 L11 L12 h10 h11 h12⟩  /-! Top-based wrappers.
--
--   The following holds (Lean statement, in the scope of module `NLogN.HNumExp2`):
--
--   ```lean
--   theorem NLogN.expNegFixP_top (s : IState HS) (h10 : s.IsInt 10) (h10' : 0 ≤ s.top 10)
--       (h11 : s.IsInt 11) (h11' : 0 ≤ s.top 11) (h12 : s.IsInt 12) :
--       expNegFixP.ok s ∧
--       expNegFixP.run s = s.upd 13 (.int (expNegFix (s.top 10).toNat (s.top 11).toNat (s.top 12)) ::
--         s.G 13) ∧
--       expNegFixP.cost s ≤ expNegFixCost (s.top 10).toNat (s.top 11).toNat (zsz (s.top 12))
--         ((-(s.top 12)) / log2Bits (s.top 11).toNat).toNat
--   ```
--
--   **Context.** The lemma belongs to the part *`expNegFix`, `expNeg`, `expPos` as register programs*: `expNegFixP`: inputs `n` on `10`, `M` on `11`, `X` on `12`; result pushed on `13`.
--   Uses (with pushes popped) registers `3 … 9` and the scratch registers of `log2P`
--   (`0, 1, 2, 40 … 47`) and `expP` (`30 … 39`).
--
--   **Formalization Note.** This is a lemma of the Lean development `NLogN`, a multitape-Turing-machine implementation of the Harvey–van der Hoeven $O(n\log n)$ integer multiplication algorithm, used in the proof of `NLogN.FIN.theorem_1_1_nlogn : IntMul.MulTimeBound fun n => n * Real.log n`. All names refer to the definition bundles `IntMul_HvdH_M_Defs1`–`IntMul_HvdH_M_Defs8` (namespace `NLogN`), built on the platform model `Def_IntMul_MultitapeModel` and the published reference `Def_IntMul_HvdH_MachineRef`. The machine layer: `IState HS` is a state of 64 item stacks; `RM` programs have a semantics `p.run s`, a definedness predicate `p.ok M s` and a cost `p.cost M s` relative to a multiplication spec `M : MulSpec`; `zsz z` is the bit length of $|z|$.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), 563–617 (Theorem 1.1: multitape Turing machine multiplication in O(n log n)). Lemma `NLogN.expNegFixP_top` of the Lean development NLogN/HNumExp2.lean (lines 303–313), written for the prove2.me integer-multiplication campaign.

-- Harvey–van der Hoeven multitape-TM development (NLogN), generated by skeleton subtraction.

import Definitions.Def_IntMul_HvdH_M_Defs8

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
open NLogN
open IntMul RS IntMul.HvdH

theorem NLogN.expNegFixP_top (s : IState HS) (h10 : s.IsInt 10) (h10' : 0 ≤ s.top 10)
    (h11 : s.IsInt 11) (h11' : 0 ≤ s.top 11) (h12 : s.IsInt 12) :
    expNegFixP.ok s ∧
    expNegFixP.run s = s.upd 13 (.int (expNegFix (s.top 10).toNat (s.top 11).toNat (s.top 12)) ::
      s.G 13) ∧
    expNegFixP.cost s ≤ expNegFixCost (s.top 10).toNat (s.top 11).toNat (zsz (s.top 12))
      ((-(s.top 12)) / log2Bits (s.top 11).toNat).toNat := by sorry
