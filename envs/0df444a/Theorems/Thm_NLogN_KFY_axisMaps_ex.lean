-- Prove2me | Theorems.Thm_NLogN_KFY_axisMaps_ex
-- name    : NLogN.KFY.axisMaps_ex
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-17T08:54:48.056598+00:00
-- url     : https://prove2.me/theorems/0358e6e0-b0c8-4ce0-88cc-315bee23519a
-- title:
--   No prc node. -/ def noPrc : RM → Bool | .rs _ | .mul _ _ _ | .op _ => true | .seq a b | .ite _ a b =>…
-- statement:
--   No `prc` node. -/ def noPrc : RM → Bool | .rs _ | .mul _ _ _ | .op _ => true | .seq a b | .ite _ a b => noPrc a && noPrc b | .rep _ _ b => noPrc b | .prc .. => false  theorem prcOK_of_noPrc {P : ℕ} {I : List Sym} {iprog : Fin P → IStmt HS P} (pc : ℕ → Fin P) : ∀ p : RM, noPrc p = true → RM.PrcOK I iprog pc p | .rs q, _ => prcOK_rs pc q | .mul k i j, _ => prcOK_mul pc k i j | .op o, _ => prcOK_op pc o | .seq a b, h => by simp only [noPrc, Bool.and_eq_true] at h exact prcOK_seq pc (prcOK_of_noPrc pc a h.1) (prcOK_of_noPrc pc b h.2) | .ite _ a b, h => by simp only [noPrc, Bool.and_eq_true] at h exact prcOK_ite pc (prcOK_of_noPrc pc a h.1) (prcOK_of_noPrc pc b h.2) | .rep _ _ b, h => prcOK_rep pc (prcOK_of_noPrc pc b h) | .prc .., h => by simp [noPrc] at h  theorem noPrc_sap : noPrc sapAxQ = true := by decide  theorem noPrc_bap : noPrc bap0AxQ = true := by decide  section prc  variable {P : ℕ} {I : List Sym} {iprog : Fin P → IStmt HS P} {jT : Fin P} {X Y dT : Fin HS} {Kc : ℝ} (hT : TrHyp I iprog jT dT Kc) (hdT : dT ≠ 0) (hXY : X ≠ Y) (hXD : X ≠ dT) (hYD : Y ≠ dT) (hX0 : X ≠ 0) (pc : ℕ → Fin P) (hW : iprog (pc 1) = trW X Y dT jT) include hT hdT hXY hXD hYD hX0 hW  theorem prcOK_trBlk (rw rm : Fin HS) : RM.PrcOK I iprog pc (trBlk X Kc rw rm) := prcOK_seq pc (prcOK_op pc _) (prcOK_seq pc (prcOK_rs pc _) (trPrc_ok hT hdT hXY hXD hYD hX0 pc hW))  theorem prcOK_progA : RM.PrcOK I iprog pc (progA X Kc) := by have h1 := prcOK_trBlk hT hdT hXY hXD hYD hX0 pc hW zw zm have h2 := prcOK_of_noPrc (I := I) (iprog := iprog) pc _ noPrc_sap refine prcOK_seq pc (prcOK_rs pc _) (prcOK_seq pc (prcOK_rep pc ?_) (prcOK_rs pc _)) exact prcOK_seq pc (prcOK_rs pc _) (prcOK_brk pc _ (prcOK_brk pc _ (prcOK_seq pc (prcOK_brk pc _ h1) (prcOK_brk pc _ h2))))  theorem prcOK_progB : RM.PrcOK I iprog pc (progB X Kc) := by have h1 := prcOK_trBlk hT hdT hXY hXD hYD hX0 pc hW zw zm have h2 := prcOK_of_noPrc (I := I) (iprog := iprog) pc _ noPrc_bap refine prcOK_seq pc (prcOK_rs pc _) (prcOK_seq pc (prcOK_rep pc ?_) (prcOK_rs pc _)) exact prcOK_seq pc (prcOK_rs pc _) (prcOK_brk pc _ (prcOK_brk pc _ (prcOK_seq pc (prcOK_rs pc _) (prcOK_seq pc (prcOK_seq pc (prcOK_brk pc _ h1) (prcOK_brk pc _ h2)) (prcOK_rs pc _)))))  end prc  /-! ## The descriptor and the arrays -/  theorem descLineN_eq (n : ℕ) : KFM.descLineN n = descL (pP n) (αP n) (ℓP n - 1) (dP n) (KFM.dpN n) (srcsN n) := by simp [KFM.descLineN, KFM.descLine, descL, KFM.bitsZ, bitL, KFM.bLn, srcsN]  theorem discL_of_getD {p : ℕ} {L : List GI} (h : ∀ x, ‖IntMul.HvdH.gC (L.getD x 0)‖ ≤ 2 ^ p) : DiscL p L := by intro z hz obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz have := h i rwa [List.getD_eq_getElem _ _ hi] at this  theorem encK_upd0 (s : IState HS) (f : Fin HS → List ℤ) (L l : List ℤ) : (encK s f).upd 0 (ints L ++ (ints l ++ s.G 0)) = encK s (Function.update f 0 (L ++ l)) := by apply IState.ext' _ (by rfl) (by rfl) intro j by_cases hj : j = 0 · subst hj; simp [ints] · simp [hj]  theorem encK_G0 (s : IState HS) (f : Fin HS → List ℤ) (L l : List ℤ) (h : f 0 = L ++ l) : (encK s f).G 0 = ints L ++ (ints l ++ s.G 0) := by simp [h, ints]  /-! ## The axis maps exist
--
--   The following holds (Lean statement, in the scope of module `Solutions.KFY21Main`):
--
--   ```lean
--   theorem NLogN.KFY.axisMaps_ex : ∃ n₂, ∀ n, IntMul.OpenAI.Glue.n0 ≤ n → n₂ ≤ n →
--       ∀ [∀ i, NeZero (KFM.sB n i)] [∀ i, NeZero (KFM.tB n i)],
--       Nonempty (KFM.AxisMaps (d := IntMul.OpenAI.Glue.dP n) (pP n) (αP n) (KFM.sB n) (KFM.tB n))
--   ```
--
--   **Context.** The lemma belongs to the part *KFY 21: `TransNeed → LineNeed`*: The descriptor stack is `dS = 26`; `C₀ = 17 K + 1 + 216·10^14 · cZ · 4 · 58^6`, `A = 6`.
--
--   **Formalization Note.** This lemma belongs to layer 5 of the Lean formalization (integer-multiplication-kappa campaign) of the OpenAI preprint *Integer multiplication below $n\log n$*: the uniform item-language machine (register programs over the `NLogN` multitape framework) assembling the Proposition 14 / Lemma 13 / Proposition 18 pieces, the resampling and chirp stages and the cost recurrences into one fixed machine, culminating in `NLogN.KFTop.kappa_bound : IntMul.KappaBound (1 / 2 ^ 182)` (the bound of `Def_IntMul_MultitapeModel`). All names refer to the definition bundles up to `IntMul_Kappa_K_Defs33`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026. Lemma `NLogN.KFY.axisMaps_ex` of the Lean development Solutions/KFY21Main.lean (lines 140–150), integer-multiplication-kappa campaign.

-- OpenAI-preprint / κ-improvement development (integer-multiplication-kappa), generated by skeleton subtraction.

import Definitions.Def_IntMul_Kappa_K_Defs33

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
open NLogN
open NLogN.KFY
open IntMul NLogN IntMul.OpenAI.Glue NLogN.GL NLogN.AX NLogN.Rsp IntMul.HvdH.Ref KIL KFB

theorem NLogN.KFY.axisMaps_ex : ∃ n₂, ∀ n, IntMul.OpenAI.Glue.n0 ≤ n → n₂ ≤ n →
    ∀ [∀ i, NeZero (KFM.sB n i)] [∀ i, NeZero (KFM.tB n i)],
    Nonempty (KFM.AxisMaps (d := IntMul.OpenAI.Glue.dP n) (pP n) (αP n) (KFM.sB n) (KFM.tB n)) := by sorry
