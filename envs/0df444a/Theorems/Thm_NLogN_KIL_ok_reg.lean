-- Prove2me | Theorems.Thm_NLogN_KIL_ok_reg
-- name    : NLogN.KIL.ok_reg
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-17T08:41:33.153141+00:00
-- url     : https://prove2.me/theorems/1cad3aee-703b-442b-a774-b04f98fcb99c
-- title:
--   A push of an arbitrary (e.g. multiplying) expression, with the quadratic cost bound. -/ theorem Sp.pushQ…
-- statement:
--   A push of an arbitrary (e.g. multiplying) expression, with the quadratic cost bound. -/ theorem Sp.pushQ {i : Fin HS} {e : Ex HS} {B : ℕ} (hi : i.val < 56) (hc : e.Clean) (hok : e.ok (encK s f)) (hB : e.Bnd (encK s f) B) : Sp (.push i e) (encK s f) (encK s (Function.update f i (e.eval (encK s f) :: f i))) ((e.size + 1) * 10 ^ 7 * (B + 2) ^ 2) := by refine ⟨⟨hi, hc, hok⟩, ?_, ?_⟩ · simp only [run] rw [← encK_upd]; simp [ints] · exact pushCost_le e _ B hB  theorem Sp.pop {i : Fin HS} {a : ℤ} {l : List ℤ} {B : ℕ} (hi : i.val < 56) (hf : f i = a :: l) (ha : zsz a ≤ B) : Sp (.pop i) (encK s f) (encK s (Function.update f i l)) (2 * B + 2) := by refine ⟨⟨hi, isInt_encK hf⟩, ?_, ?_⟩ · simp only [run] rw [← encK_upd]; simp [hf] · simp only [cost, top_encK hf]; omega  theorem Sp.asg {i : Fin HS} {e : Ex HS} {a : ℤ} {l : List ℤ} {B : ℕ} (hi : i.val < 56) (hf : f i = a :: l) (ha : zsz a ≤ B) (hc : e.Clean) (hok : e.ok (encK s f)) (hl : e.Lin) (hB : e.Bnd (encK s f) B) : Sp (.asg i e) (encK s f) (encK s (Function.update f i (e.eval (encK s f) :: l))) ((e.size + 1) * 2000 * (B + 2)) := by refine ⟨⟨hi, hc, hok, isInt_encK hf⟩, ?_, ?_⟩ · simp only [run] rw [← encK_upd]; simp [hf, ints] · exact asgCost_le_lin i e _ B hl hB (by rw [top_encK hf]; exact ha)  end  /-! ## Moving integers between stacks -/  theorem Sp.mvK {X Y C : Fin HS} (hXY : X ≠ Y) (hXC : X ≠ C) (hYC : Y ≠ C) (hX5 : X.val < 56) (hY5 : Y.val < 56) (hC5 : C.val < 56) (s : IState HS) (f : Fin HS → List ℤ) (n : Ex HS) (hnc : n.Clean) (hno : n.ok (encK s f)) (L l : List ℤ) (hX : f X = L ++ l) (hn : n.eval (encK s f) = L.length) (B : ℕ) (hL : Bnd B L) (hnl : n.Lin) (hnb : n.Bnd (encK s f) B) : Sp (mvK X Y C n) (encK s f) (encK s (Function.update (Function.update f X l) Y (L.reverse ++ f Y))) ((n.size + 1) * 2000 * (B + 2) + L.length * (14000 * (B + 2)) + 32) := by have hXs : (encK s f).G X = ints L ++ (ints l ++ s.G X) := by simp [hX, ints_append] have H := mvK_spec hXY hXC hYC hX5 hY5 hC5 n hnc (encK s f) L _ hXs hno hn refine ⟨H.1, ?_, mvK_cost hXY hXC hYC n (encK s f) L _ hXs hn B hL hnl hnb⟩ rw [H.2] refine IState.ext' (fun j => ?_) rfl rfl by_cases h1 : j = Y · subst h1; simp [Ne.symm hXY, ints_append, ints_reverse] by_cases h2 : j = X · subst h2; simp [hXY] · simp [h1, h2]  /-! ## Counted loops through a family of managed states -/  theorem withCtr_encK (C : Fin HS) (s : IState HS) (f g : Fin HS → List ℤ) (hf : f C = []) (hg : g C = []) (N k : ℕ) : withCtr C (encK s f) N k (encK s g) = encK s (Function.update g C [(N : ℤ) - k]) := by refine IState.ext' (fun j => ?_) rfl rfl by_cases h : j = C · subst h; simp [withCtr, hf, hg] · simp [withCtr, h]  theorem Sp.rep {C : Fin HS} {n : Ex HS} {b : RS} {s : IState HS} {F : ℕ → Fin HS → List ℤ} {N B c : ℕ} (hC5 : C.val < 56) (hC : ∀ k, F k C = []) (hw : C ∉ b.writes) (hnc : n.Clean) (hno : n.ok (encK s (F 0))) (hnl : n.Lin) (hnb : n.Bnd (encK s (F 0)) B) (hn : n.eval (encK s (F 0)) = N) (hb : ∀ k < N, Sp b (encK s (Function.update (F k) C [(N : ℤ) - k])) (encK s (Function.update (F (k + 1)) C [(N : ℤ) - k])) c) : Sp (.rep C n b) (encK s (F 0)) (encK s (F N)) ((n.size + 1) * 2000 * (B + 2) + N * (c + 8000 * (B + 2) + 30) + 32) := by have hN : (n.eval (encK s (F 0))).toNat = N := by rw [hn]; simp have H : RepStates C n b (encK s (F 0)) (fun k => encK s (F k)) := { nonneg := by rw [hn]; positivity hw := hw h0 := rfl hG := fun k => by simp [hC] step := by intro k hk rw [hN] at hk ⊢ rw [withCtr_encK C s _ _ (hC 0) (hC k), withCtr_encK C s _ _ (hC 0) (hC (k + 1))] exact (hb k hk).2.1 } refine ⟨?_, ?_, ?_⟩ · refine H.ok hC5 hnc hno ?_ intro k hk rw [hN] at hk ⊢ rw [withCtr_encK C s _ _ (hC 0) (hC k)] exact (hb k hk).1 · rw [H.run, hN] · have := H.cost_le_lin B c hnl hnb (by intro k hk rw [hN] at hk ⊢ rw [withCtr_encK C s _ _ (hC 0) (hC k)] exact (hb k hk).2.2) rw [hN] at this exact this  /-! ## Expression side conditions on managed states
--
--   The following holds (Lean statement, in the scope of module `Solutions.KILBase`):
--
--   ```lean
--   theorem NLogN.KIL.ok_reg {s : IState HS} {f : Fin HS → List ℤ} {i : Fin HS} {a : ℤ} {l : List ℤ}
--       (h : f i = a :: l) : (Ex.reg i).ok (NLogN.KIL.encK s f)
--   ```
--
--   **Context.** The lemma belongs to the part *KIL base: register programs on "managed" stacks*: `encK s f` is the state `s` with the list of integers `f j` pushed on top of every stack `j`
--   (`f j = []` for unmanaged stacks).  All programs of the KIL files are specified on such states;
--   updates are `Function.update`s of `f`, which keeps the bookkeeping small.
--
--   **Formalization Note.** This lemma belongs to layer 5 of the Lean formalization (integer-multiplication-kappa campaign) of the OpenAI preprint *Integer multiplication below $n\log n$*: the uniform item-language machine (register programs over the `NLogN` multitape framework) assembling the Proposition 14 / Lemma 13 / Proposition 18 pieces, the resampling and chirp stages and the cost recurrences into one fixed machine, culminating in `NLogN.KFTop.kappa_bound : IntMul.KappaBound (1 / 2 ^ 182)` (the bound of `Def_IntMul_MultitapeModel`). All names refer to the definition bundles up to `IntMul_Kappa_K_Defs33`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026. Lemma `NLogN.KIL.ok_reg` of the Lean development Solutions/KILBase.lean (lines 194–195), integer-multiplication-kappa campaign.

-- OpenAI-preprint / κ-improvement development (integer-multiplication-kappa), generated by skeleton subtraction.

import Definitions.Def_IntMul_Kappa_K_Defs33

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
open NLogN
open IntMul RS
open NLogN.KIL

theorem NLogN.KIL.ok_reg {s : IState HS} {f : Fin HS → List ℤ} {i : Fin HS} {a : ℤ} {l : List ℤ}
    (h : f i = a :: l) : (Ex.reg i).ok (NLogN.KIL.encK s f) := by sorry
