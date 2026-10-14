-- Prove2me | Theorems.Thm_NLogN_AX_popT_all
-- name    : NLogN.AX.popT_all
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-13T12:43:01.023831+00:00
-- url     : https://prove2.me/theorems/9ab2518c-b4a8-4906-8a08-b314ae3f0318
-- title:
--   The state after `tmpP`
-- statement:
--   The state after `tmpP`. -/ def tmpSt (e s α : ℕ) (st : IState HS) : IState HS := ((st.upd xE (.int (e : ℤ) :: st.G xE)).upd xK (.int ((s ^ 2 : ℕ) : ℤ) :: st.G xK)).upd xG (.int ((2 * α ^ 2 - 2 : ℕ) : ℤ) :: st.G xG)  theorem tmpP_all (e s α B : ℕ) (st : IState HS) (hα : 1 ≤ α) (hNR : ∃ L, st.G bNR = .int ((2 * e + 1 : ℕ) : ℤ) :: L) (hS : ∃ L, st.G bS = .int (s : ℤ) :: L) (hA : ∃ L, st.G bI = .int ((α ^ 2 : ℕ) : ℤ) :: L) (hB1 : 2 * e + 2 < 2 ^ B) (hB2 : s ^ 2 < 2 ^ B) (hB3 : 2 * α ^ 2 + 2 < 2 ^ B) : tmpP.ok st ∧ tmpP.run st = tmpSt e s α st ∧ tmpP.cost st ≤ 16 * 10 ^ 7 * (B + 2) ^ 2 := by obtain ⟨L1, h1⟩ := hNR; obtain ⟨L2, h2⟩ := hS; obtain ⟨L3, h3⟩ := hA have t1 := IState.top_eq h1; have t2 := IState.top_eq h2; have t3 := IState.top_eq h3 have zl : ∀ z : ℤ, z.natAbs < 2 ^ B → zsz z ≤ B := fun z h => zsz_le_of_lt h -- step 1 have ev1 : eE.eval st = (e : ℤ) := by simp only [eE, Ex.eval, t1]; push_cast rw [show (2 * (e : ℤ) + 1 + -1) = 2 * e by ring]; simp set st1 := st.upd xE (.int (e : ℤ) :: st.G xE) with hst1 have r1 : (RS.push xE eE).run st = st1 := push_run_val _ _ _ _ ev1 have o1 : (RS.push xE eE).ok st := by refine ⟨by decide, by simp (config := {decide := true}) [eE, Ex.Clean, Ex.regs, zX_all], ?_⟩ exact ⟨⟨IState.isInt_of h1, trivial⟩, trivial, ⟨1, by simp [Ex.eval]⟩⟩ have b1 : eE.Bnd st B := by have two : 2 < 2 ^ B := by omega simp only [eE, Ex.Bnd, Ex.eval, t1] refine ⟨⟨zl _ ?_, zl _ ?_, zl _ ?_⟩, zl _ ?_⟩ · rw [Int.natAbs_natCast]; omega · show (1 : ℕ) < 2 ^ B; omega · rw [show ((2 * e + 1 : ℕ) : ℤ) + -1 = ((2 * e : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]; omega · show (2 : ℕ) < 2 ^ B; omega have c1 := RS.pushCost_le eE st B b1 -- step 2 have g2 : st1.G bS = .int (s : ℤ) :: L2 := by simp (config := {decide := true}) [hst1, h2] have u2 := IState.top_eq g2 have ev2 : s2E.eval st1 = ((s ^ 2 : ℕ) : ℤ) := by simp [s2E, Ex.eval, u2]; ring set st2 := st1.upd xK (.int ((s ^ 2 : ℕ) : ℤ) :: st1.G xK) with hst2 have r2 : (RS.push xK s2E).run st1 = st2 := push_run_val _ _ _ _ ev2 have o2 : (RS.push xK s2E).ok st1 := by refine ⟨by decide, by simp (config := {decide := true}) [s2E, Ex.Clean, Ex.regs, zX_all], ?_⟩ exact ⟨IState.isInt_of g2, IState.isInt_of g2⟩ have b2 : s2E.Bnd st1 B := by simp only [s2E, Ex.Bnd, Ex.eval, u2] refine ⟨zl _ (by simp; nlinarith), zl _ (by simp; nlinarith), zl _ ?_⟩ rw [show (s : ℤ) * s = ((s ^ 2 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]; exact hB2 have c2 := RS.pushCost_le s2E st1 B b2 -- step 3 have g3 : st2.G bI = .int ((α ^ 2 : ℕ) : ℤ) :: L3 := by simp (config := {decide := true}) [hst2, hst1, h3] have u3 := IState.top_eq g3 have ev3 : gE.eval st2 = ((2 * α ^ 2 - 2 : ℕ) : ℤ) := by simp only [gE, Ex.eval, u3] have : 2 ≤ 2 * α ^ 2 := by nlinarith push_cast [this]; ring have r3 : (RS.push xG gE).run st2 = tmpSt e s α st := by rw [push_run_val _ _ _ _ ev3]; simp only [tmpSt, hst2, hst1] have a1 : (st.upd xE (Item.int ↑e :: st.G xE)).G xK = st.G xK := by simp (config := {decide := true}) have a2 : ((st.upd xE (Item.int ↑e :: st.G xE)).upd xK (Item.int ↑(s ^ 2) :: st.G xK)).G xG = st.G xG := by simp (config := {decide := true}) rw [a1, a2] have o3 : (RS.push xG gE).ok st2 := by refine ⟨by decide, by simp (config := {decide := true}) [gE, Ex.Clean, Ex.regs, zX_all], ?_⟩ exact ⟨⟨IState.isInt_of g3, IState.isInt_of g3⟩, trivial⟩ have b3 : gE.Bnd st2 B := by have hα2 : 1 ≤ α ^ 2 := Nat.one_le_pow _ _ hα simp only [gE, Ex.Bnd, Ex.eval, u3] refine ⟨⟨zl _ (by simp; omega), zl _ (by simp; omega), zl _ ?_⟩, zl _ (by simp; omega), zl _ ?_⟩ · rw [show ((α ^ 2 : ℕ) : ℤ) + ((α ^ 2 : ℕ) : ℤ) = ((2 * α ^ 2 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]; omega · rw [show ((α ^ 2 : ℕ) : ℤ) + ((α ^ 2 : ℕ) : ℤ) + -2 = ((2 * α ^ 2 - 2 : ℕ) : ℤ) by push_cast [show 2 ≤ 2 * α ^ 2 by omega]; ring, Int.natAbs_natCast]; omega have c3 := RS.pushCost_le gE st2 B b3 refine ⟨⟨o1, by rw [r1]; exact ⟨o2, by rw [r2]; exact o3⟩⟩, ?_, ?_⟩ · show (RS.push xG gE).run ((RS.push xK s2E).run ((RS.push xE eE).run st)) = _ rw [r1, r2, r3] · show (RS.push xE eE).cost st + ((RS.push xK s2E).cost ((RS.push xE eE).run st) + (RS.push xG gE).cost ((RS.push xK s2E).run ((RS.push xE eE).run st))) ≤ _ rw [r1, r2] simp only [RS.cost] rw [show eE.size = 5 from rfl] at c1 rw [show s2E.size = 3 from rfl] at c2 rw [show gE.size = 5 from rfl] at c3 generalize (B + 2) ^ 2 = Y at * omega  theorem tmpQ_all (e s α B : ℕ) (st : IState HS) (hB1 : 2 * e + 2 < 2 ^ B) (hB2 : s ^ 2 < 2 ^ B) (hB3 : 2 * α ^ 2 + 2 < 2 ^ B) (st' : IState HS) (h1 : st'.G xE = .int (e : ℤ) :: st.G xE) (h2 : st'.G xK = .int ((s ^ 2 : ℕ) : ℤ) :: st.G xK) (h3 : st'.G xG = .int ((2 * α ^ 2 - 2 : ℕ) : ℤ) :: st.G xG) : tmpQ.ok st' ∧ tmpQ.run st' = ((st'.upd xG (st.G xG)).upd xK (st.G xK)).upd xE (st.G xE) ∧ tmpQ.cost st' ≤ 6 * B + 6 := by have zl : ∀ z : ℤ, z.natAbs < 2 ^ B → zsz z ≤ B := fun z h => zsz_le_of_lt h have q1 : (RS.pop xG).run st' = st'.upd xG (st.G xG) := pop_run_val _ _ _ _ h3 have g2 : (st'.upd xG (st.G xG)).G xK = .int ((s ^ 2 : ℕ) : ℤ) :: st.G xK := by simp (config := {decide := true}) [h2] have q2 := pop_run_val _ _ _ _ g2 have g3 : ((st'.upd xG (st.G xG)).upd xK (st.G xK)).G xE = .int (e : ℤ) :: st.G xE := by simp (config := {decide := true}) [h1] have q3 := pop_run_val _ _ _ _ g3 refine ⟨⟨⟨by decide, IState.isInt_of h3⟩, ?_⟩, ?_, ?_⟩ · rw [q1]; exact ⟨⟨by decide, IState.isInt_of g2⟩, by rw [q2]; exact ⟨by decide, IState.isInt_of g3⟩⟩ · show (RS.pop xE).run ((RS.pop xK).run ((RS.pop xG).run st')) = _ rw [q1, q2, q3] · show (RS.pop xG).cost st' + ((RS.pop xK).cost ((RS.pop xG).run st') + (RS.pop xE).cost ((RS.pop xK).run ((RS.pop xG).run st'))) ≤ _ rw [q1, q2] have k1 := cpop xG st' B (by rw [IState.top_eq h3]; exact zl _ (by simp; omega)) have k2 := cpop xK _ B (by rw [IState.top_eq g2]; exact zl _ (by simp; omega)) have k3 := cpop xE _ B (by rw [IState.top_eq g3]; exact zl _ (by simp; omega)) omega  /-! ## Removing a table
--
--   The following holds (Lean statement, in the scope of module `NLogN.HAx7`):
--
--   ```lean
--   theorem NLogN.AX.popT_all (M : MulSpec) (X r : Fin HS) (st : IState HS) (L : List ℤ) (R : List Item)
--       (N B : ℕ) (hXC : X ≠ gCC) (hX : X.val < 56) (hr : r.val < 56)
--       (hXs : st.G X = ints L ++ R) (hN : ∃ LL, st.G r = .int (N : ℤ) :: LL) (hl : L.length = N)
--       (hLB : ∀ y ∈ L, zsz y ≤ B) (hNB : zsz (N : ℤ) ≤ B) :
--       (RM.rs (popK X gCC (.reg r))).run st = st.upd X R ∧ (RM.rs (popK X gCC (.reg r))).ok M st ∧
--         (RM.rs (popK X gCC (.reg r))).cost M st ≤ 2 * 2000 * (B + 2) + N * (12000 * (B + 2)) + 32
--   ```
--
--   **Context.** The lemma belongs to the part *One resampling axis, part 7: derived scalars and table removal for the `B̃` axis*.
--
--   **Formalization Note.** This is a lemma of the Lean development `NLogN`, a multitape-Turing-machine implementation of the Harvey–van der Hoeven $O(n\log n)$ integer multiplication algorithm, used in the proof of `NLogN.FIN.theorem_1_1_nlogn : IntMul.MulTimeBound fun n => n * Real.log n`. All names refer to the definition bundles `IntMul_HvdH_M_Defs1`–`IntMul_HvdH_M_Defs8` (namespace `NLogN`), built on the platform model `Def_IntMul_MultitapeModel` and the published reference `Def_IntMul_HvdH_MachineRef`. The machine layer: `IState HS` is a state of 64 item stacks; `RM` programs have a semantics `p.run s`, a definedness predicate `p.ok M s` and a cost `p.cost M s` relative to a multiplication spec `M : MulSpec`; `zsz z` is the bit length of $|z|$.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), 563–617 (Theorem 1.1: multitape Turing machine multiplication in O(n log n)). Lemma `NLogN.AX.popT_all` of the Lean development NLogN/HAx7.lean (lines 140–154), written for the prove2.me integer-multiplication campaign.

-- Harvey–van der Hoeven multitape-TM development (NLogN), generated by skeleton subtraction.

import Definitions.Def_IntMul_HvdH_M_Defs8

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
open NLogN
open NLogN.AX
open IntMul NLogN IntMul.HvdH.Ref NLogN.GL NLogN.Rsp

theorem NLogN.AX.popT_all (M : MulSpec) (X r : Fin HS) (st : IState HS) (L : List ℤ) (R : List Item)
    (N B : ℕ) (hXC : X ≠ gCC) (hX : X.val < 56) (hr : r.val < 56)
    (hXs : st.G X = ints L ++ R) (hN : ∃ LL, st.G r = .int (N : ℤ) :: LL) (hl : L.length = N)
    (hLB : ∀ y ∈ L, zsz y ≤ B) (hNB : zsz (N : ℤ) ≤ B) :
    (RM.rs (popK X gCC (.reg r))).run st = st.upd X R ∧ (RM.rs (popK X gCC (.reg r))).ok M st ∧
      (RM.rs (popK X gCC (.reg r))).cost M st ≤ 2 * 2000 * (B + 2) + N * (12000 * (B + 2)) + 32 := by sorry
