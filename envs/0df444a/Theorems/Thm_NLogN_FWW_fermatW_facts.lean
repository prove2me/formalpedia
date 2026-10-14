-- Prove2me | Theorems.Thm_NLogN_FWW_fermatW_facts
-- name    : NLogN.FWW.fermatW_facts
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-13T12:49:08.906984+00:00
-- url     : https://prove2.me/theorems/528f8c00-10df-47ce-b6f6-be9ee4cb434e
-- title:
--   `8 (K - 1)`: the number of descriptor integers
-- statement:
--   `8 (K - 1)`: the number of descriptor integers. -/ def cD : Ex HS := .shl (.reg wKM) (.lit 8)  theorem cT_facts (t : IState HS) (N e B : ℕ) (L1 L2 : List Item) (h1 : t.G wLO = .int (N : ℤ) :: L1) (h2 : t.G KR = .int ((2 ^ e : ℕ) : ℤ) :: L2) (hN : 1 ≤ N) (hB : zsz ((2 * N * 2 ^ e : ℕ) : ℤ) ≤ B) : cT.eval t = ((2 * N * 2 ^ e : ℕ) : ℤ) ∧ cT.Clean ∧ cT.ok t ∧ cT.Lin ∧ cT.Bnd t B := by have e1 := IState.top_eq h1 have e2 := IState.top_eq h2 have hr : 1 ≤ 2 ^ e := Nat.one_le_two_pow have hNle : N ≤ 2 * N * 2 ^ e := by nlinarith have h2N : N + N ≤ 2 * N * 2 ^ e := by nlinarith have hrle : 2 ^ e ≤ 2 * N * 2 ^ e := by nlinarith refine ⟨?_, ?_, ?_, ⟨⟨trivial, trivial⟩, trivial⟩, ?_⟩ · simp only [cT, Ex.eval, e1, e2]; push_cast; ring · intro i hi simp only [cT, Ex.regs, List.mem_append, List.mem_singleton] at hi rcases hi with (rfl | rfl) | rfl <;> simp (config := {decide := true}) [zX_all] · refine ⟨⟨IState.isInt_of h1, IState.isInt_of h1⟩, IState.isInt_of h2, e, ?_⟩ simp [Ex.eval, e2] · simp only [cT, Ex.Bnd, Ex.eval, e1, e2] refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ · exact (zsz_mono (by simp only [Int.natAbs_natCast]; omega)).trans hB · exact (zsz_mono (by simp only [Int.natAbs_natCast]; omega)).trans hB · exact (zsz_mono (by rw [show (N : ℤ) + N = ((N + N : ℕ) : ℤ) by push_cast; ring] simp only [Int.natAbs_natCast]; omega)).trans hB · exact (zsz_mono (by simp only [Int.natAbs_natCast]; omega)).trans hB · rw [show ((N : ℤ) + N) * ((2 ^ e : ℕ) : ℤ) = ((2 * N * 2 ^ e : ℕ) : ℤ) by push_cast; ring] exact hB  theorem cD_facts (t : IState HS) (k B : ℕ) (L : List Item) (h : t.G wKM = .int (k : ℤ) :: L) (hB : zsz ((8 * k : ℕ) : ℤ) ≤ B) (h8 : 4 ≤ B) : cD.eval t = ((8 * k : ℕ) : ℤ) ∧ cD.Clean ∧ cD.ok t ∧ cD.Lin ∧ cD.Bnd t B := by have e1 := IState.top_eq h refine ⟨?_, ?_, ?_, ⟨trivial, trivial⟩, ?_⟩ · simp only [cD, Ex.eval, e1]; push_cast; ring · intro i hi simp only [cD, Ex.regs, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hi subst hi; simp (config := {decide := true}) [zX_all] · exact ⟨IState.isInt_of h, trivial, 3, by simp [Ex.eval]⟩ · simp only [cD, Ex.Bnd, Ex.eval, e1] refine ⟨?_, ?_, ?_⟩ · exact (zsz_mono (by simp only [Int.natAbs_natCast]; omega)).trans hB · exact (zsz_le_of_lt (by norm_num)).trans h8 · rw [show (k : ℤ) * 8 = ((8 * k : ℕ) : ℤ) by push_cast; ring]; exact hB  /-! ## Order-preserving transfers as `Spec`s -/  theorem spec_xfer (M : MulSpec) (i j : Fin HS) (n : Ex HS) (s : IState HS) (l : List ℤ) (Ri : List Item) (B : ℕ) (hij : i ≠ j) (hiT : i ≠ GL.gZT) (hjT : j ≠ GL.gZT) (hiV : i ≠ GL.gCV) (hjV : j ≠ GL.gCV) (hi55 : i.val < 55) (hj55 : j.val < 55) (hi : s.G i = ints l ++ Ri) (hn : n.eval s = l.length) (hnc : n.Clean) (hno : n.ok s) (hl : n.Lin) (hnB : n.Bnd s B) (hB : ∀ x ∈ l, zsz x ≤ B) (hnr : ∀ t : IState HS, (∀ x, x ≠ i → x ≠ GL.gZT → t.G x = s.G x) → n.eval t = n.eval s ∧ n.ok t ∧ n.Bnd t B) : Spec M (GL.xferP i j n) s ((s.upd i Ri).upd j (ints l ++ s.G j)) (2 * ((n.size + 1) * 2000 * (B + 2) + l.length * (14000 * (B + 2) + 30) + 32)) := by obtain ⟨a, b, c⟩ := GL.xferP_all M i j n s l Ri B hij hiT hjT hiV hjV hi55 hj55 hi hn hnc hno hl hnB hB hnr exact ⟨b, a, c⟩  /-! ## Facts about `fermatW`
--
--   The following holds (Lean statement, in the scope of module `NLogN.HFwW1`):
--
--   ```lean
--   theorem NLogN.FWW.fermatW_facts (M : MulSpec) (q : Ref.Params) (kb : ℕ) (hP : 1 ≤ q.P)
--       (hkb : q.logOuter ≤ kb) (U V : List (ℤ × ℤ))
--       (hUl : U.length = 2 ^ q.logOuter * q.r) (hVl : V.length = 2 ^ q.logOuter * q.r) :
--       (Ref.fermatW q U V).length = 2 ^ q.logOuter * q.r ∧
--         ∀ p ∈ Ref.fermatW q U V, |p.1| < 2 ^ (q.P + 2) ∧ |p.2| < 2 ^ (q.P + 2)
--   ```
--
--   **Context.** The lemma belongs to the part *Wrapping the Fermat convolution `fwP` as an abstract `LProg2` (part 1)*.
--
--   **Formalization Note.** This is a lemma of the Lean development `NLogN`, a multitape-Turing-machine implementation of the Harvey–van der Hoeven $O(n\log n)$ integer multiplication algorithm, used in the proof of `NLogN.FIN.theorem_1_1_nlogn : IntMul.MulTimeBound fun n => n * Real.log n`. All names refer to the definition bundles `IntMul_HvdH_M_Defs1`–`IntMul_HvdH_M_Defs8` (namespace `NLogN`), built on the platform model `Def_IntMul_MultitapeModel` and the published reference `Def_IntMul_HvdH_MachineRef`. The machine layer: `IState HS` is a state of 64 item stacks; `RM` programs have a semantics `p.run s`, a definedness predicate `p.ok M s` and a cost `p.cost M s` relative to a multiplication spec `M : MulSpec`; `zsz z` is the bit length of $|z|$.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), 563–617 (Theorem 1.1: multitape Turing machine multiplication in O(n log n)). Lemma `NLogN.FWW.fermatW_facts` of the Lean development NLogN/HFwW1.lean (lines 124–173), written for the prove2.me integer-multiplication campaign.

-- Harvey–van der Hoeven multitape-TM development (NLogN), generated by skeleton subtraction.

import Definitions.Def_IntMul_HvdH_M_Defs8

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open NLogN
open NLogN.FWW
open IntMul IntMul.HvdH NLogN NLogN.FW

theorem NLogN.FWW.fermatW_facts (M : MulSpec) (q : Ref.Params) (kb : ℕ) (hP : 1 ≤ q.P)
    (hkb : q.logOuter ≤ kb) (U V : List (ℤ × ℤ))
    (hUl : U.length = 2 ^ q.logOuter * q.r) (hVl : V.length = 2 ^ q.logOuter * q.r) :
    (Ref.fermatW q U V).length = 2 ^ q.logOuter * q.r ∧
      ∀ p ∈ Ref.fermatW q U V, |p.1| < 2 ^ (q.P + 2) ∧ |p.2| < 2 ^ (q.P + 2) := by sorry
