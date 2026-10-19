-- Prove2me | Theorems.Thm_NLogN_KFM_parS_cost
-- name    : NLogN.KFM.parS_cost
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-17T08:48:27.48381+00:00
-- url     : https://prove2.me/theorems/d8591af4-effc-4d0d-be50-0c758b379606
-- title:
--   Sizes of the small values. -/ theorem zszQ {b : ℕ} {z : ℤ} (h : |z| ≤ 2 ^ (b + 1)) : zsz z ≤ 8 * b + 8 :=…
-- statement:
--   Sizes of the small values. -/ theorem zszQ {b : ℕ} {z : ℤ} (h : |z| ≤ 2 ^ (b + 1)) : zsz z ≤ 8 * b + 8 := KFL.zsz_le_of_abs (lt_of_le_of_lt h (pow_lt_pow_right₀ (by norm_num) (by omega)))  theorem gam_le {n : ℕ} (hn : n0 ≤ n) : 8 * dP n * αP n ^ 2 ≤ bP n := by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hγ, -⟩ := params_ok hn unfold γP at hγ have : ((8 * dP n * αP n ^ 2 : ℕ) : ℝ) ≤ (bP n : ℝ) := by push_cast; linarith exact_mod_cast this  theorem alpha_pos {n : ℕ} (hn : n0 ≤ n) : 1 ≤ αP n := by obtain ⟨-, -, hb, hd, -, -, -, -, -, -, -, -, -, -, -, h12, -⟩ := params_ok hn by_contra h0 have : αP n = 0 := by omega rw [this] at h12 have : (1 : ℝ) ≤ dP n := by exact_mod_cast hd have : (8192 : ℝ) ≤ bP n := by exact_mod_cast hb norm_num at h12 nlinarith  theorem b_pow {n : ℕ} (hn : n0 ≤ n) : 8 * bP n + 100 ≤ 2 ^ bP n := by have hb := (setup_facts hn).1 have := cube_lt_pow (bP n) (by omega) have : bP n ≤ bP n ^ 3 := Nat.le_self_pow (by norm_num) _ omega  set_option maxHeartbeats 4000000 in theorem parQ_bnd {n : ℕ} (hn : n0 ≤ n) (S : ℕ) (hS : S < 2 ^ bP n) (t : IState HS) (h : QRegs t n S) : PBnd (8 * bP n + 8) Lq t := by obtain ⟨hb8, hd1, hdb, -⟩ := setup_facts hn obtain ⟨hT1, -, hLb, -⟩ := L_facts hn have hn2 := n_le hn have hγ := gam_le hn have hbp := b_pow hn have hα0 := alpha_pos hn have hα1 : αP n ^ 2 ≤ bP n := by nlinarith set M := (n + bP n - 1) / bP n with hM have hn1 : 3 ≤ n := n0_ge3 hn have hMn : M ≤ n := by rw [hM]; apply Nat.div_le_of_le_mul have : n + bP n ≤ bP n * n := by nlinarith omega obtain ⟨LL, hLL⟩ := h.hL obtain ⟨LN, hNN⟩ := h.hN obtain ⟨LB, hBB⟩ := h.hB obtain ⟨LD, hDD⟩ := h.hD obtain ⟨LA, hAA⟩ := h.hA obtain ⟨LS, hSS⟩ := h.hS have hMq : ((n : ℤ) + ((bP n : ℤ) + -1)) / (bP n : ℤ) = (M : ℤ) := by rw [show (n : ℤ) + ((bP n : ℤ) + -1) = ((n + bP n - 1 : ℕ) : ℤ) by omega, hM]; norm_cast have eγ : 2 * (dP n : ℤ) * ((αP n : ℤ) * (αP n : ℤ)) = ((2 * dP n * αP n ^ 2 : ℕ) : ℤ) := by push_cast; ring have zP : (2 : ℤ) ^ (bP n + 1) = 2 * 2 ^ bP n := by rw [pow_succ]; ring have zb : (8 * (bP n : ℤ) + 100) ≤ 2 ^ bP n := by exact_mod_cast hbp have zn : (n : ℤ) ≤ 2 ^ bP n := by exact_mod_cast hn2 have zS : (S : ℤ) < 2 ^ bP n := by exact_mod_cast hS have zM : (M : ℤ) ≤ n := by exact_mod_cast hMn have zγ : ((2 * dP n * αP n ^ 2 : ℕ) : ℤ) ≤ bP n := by push_cast; push_cast at hγ; nlinarith have zα : (αP n : ℤ) * αP n ≤ bP n := by have : ((αP n ^ 2 : ℕ) : ℤ) ≤ bP n := by exact_mod_cast hα1 push_cast at this; nlinarith have zd : (2 : ℤ) * dP n ≤ bP n := by have : dP n ≤ dP n * αP n ^ 2 := Nat.le_mul_of_pos_right _ (by positivity) have : 2 * dP n ≤ bP n := by nlinarith exact_mod_cast this have zL : (LP n : ℤ) < bP n := by exact_mod_cast hLb simp (config := {decide := true}) [Lq, PBnd, Ex.Bnd, Ex.eval, IState.top, IState.upd_G, hLL, hNN, hBB, hDD, hAA, hSS, hMq, eγ] constructorm* _ ∧ _ all_goals first | omega | (apply zszQ; rw [abs_le, zP]; constructor <;> nlinarith) | (push_cast at zγ ⊢; nlinarith) | skip  /-! ## `parS`
--
--   The following holds (Lean statement, in the scope of module `Solutions.KFMSetC`):
--
--   ```lean
--   theorem NLogN.KFM.parS_cost {n : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n) (t : IState HS) (LD LB : List Item)
--       (hD : t.G zD = .int (IntMul.OpenAI.Glue.dP n : ℤ) :: LD) (hB : t.G NLogN.KFM.zB = .int (bP n : ℤ) :: LB)
--       (h : SrcRegs t (dpN n) (srcQ (IntMul.OpenAI.Glue.dP n) (IntMul.OpenAI.Glue.rP n)) (srcM (IntMul.OpenAI.Glue.dP n) (IntMul.OpenAI.Glue.rP n) (IntMul.OpenAI.Glue.rP n / 2))
--         (srcM (IntMul.OpenAI.Glue.dP n) (IntMul.OpenAI.Glue.rP n) (IntMul.OpenAI.Glue.rP n))) :
--       parS.cost t ≤ 100 * (10 ^ 7 * (16 * bP n + 17 + 2) ^ 2) * (IntMul.OpenAI.Glue.dP n + 2)
--   ```
--
--   **Context.** The lemma belongs to the part *KFM SetC: the cost of the parameter pushes*.
--
--   **Formalization Note.** This lemma belongs to layer 5 of the Lean formalization (integer-multiplication-kappa campaign) of the OpenAI preprint *Integer multiplication below $n\log n$*: the uniform item-language machine (register programs over the `NLogN` multitape framework) assembling the Proposition 14 / Lemma 13 / Proposition 18 pieces, the resampling and chirp stages and the cost recurrences into one fixed machine, culminating in `NLogN.KFTop.kappa_bound : IntMul.KappaBound (1 / 2 ^ 182)` (the bound of `Def_IntMul_MultitapeModel`). All names refer to the definition bundles up to `IntMul_Kappa_K_Defs33`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026. Lemma `NLogN.KFM.parS_cost` of the Lean development Solutions/KFMSetC.lean (lines 147–267), integer-multiplication-kappa campaign.

-- OpenAI-preprint / κ-improvement development (integer-multiplication-kappa), generated by skeleton subtraction.

import Definitions.Def_IntMul_Kappa_K_Defs33

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open NLogN
open NLogN.KFM
open IntMul IntMul.OpenAI.Glue RS
set_option maxHeartbeats 4000000

theorem NLogN.KFM.parS_cost {n : ℕ} (hn : IntMul.OpenAI.Glue.n0 ≤ n) (t : IState HS) (LD LB : List Item)
    (hD : t.G zD = .int (IntMul.OpenAI.Glue.dP n : ℤ) :: LD) (hB : t.G NLogN.KFM.zB = .int (bP n : ℤ) :: LB)
    (h : SrcRegs t (dpN n) (srcQ (IntMul.OpenAI.Glue.dP n) (IntMul.OpenAI.Glue.rP n)) (srcM (IntMul.OpenAI.Glue.dP n) (IntMul.OpenAI.Glue.rP n) (IntMul.OpenAI.Glue.rP n / 2))
      (srcM (IntMul.OpenAI.Glue.dP n) (IntMul.OpenAI.Glue.rP n) (IntMul.OpenAI.Glue.rP n))) :
    parS.cost t ≤ 100 * (10 ^ 7 * (16 * bP n + 17 + 2) ^ 2) * (IntMul.OpenAI.Glue.dP n + 2) := by sorry
