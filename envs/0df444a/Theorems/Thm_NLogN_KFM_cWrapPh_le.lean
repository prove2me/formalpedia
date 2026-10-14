-- Prove2me | Theorems.Thm_NLogN_KFM_cWrapPh_le
-- name    : NLogN.KFM.cWrapPh_le
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-14T05:24:40.434801+00:00
-- url     : https://prove2.me/theorems/caf3d561-e88e-4222-b551-c8e2acf9a326
-- title:
--   Proposition 14 around any IStmt C-layer, with one-pass phases. -/ theorem p14Ph_iruns (hρ : ρ < K) (hD : 1…
-- statement:
--   **Proposition 14 around any `IStmt` `C`-layer, with one-pass phases.** -/ theorem p14Ph_iruns (hρ : ρ < K) (hD : 1 ≤ D) {r p w : ℕ} (hr : 1 ≤ r) (hS : 1 ≤ S) (hP : 1 ≤ P) {Cc : ℕ → IStmt HS Pp} {E dC : ℕ} {kC : ℕ → ℕ} (hCimpl : SImplI Isym iprog r (fun i : Fin D => KFH.stT K D S ρ i) (vol (Butterfly.layerShape P K D S)) (tens Cm : Butterfly.Op (Fin D)) Cc E dC kC) (s : IState HS) (f : Fin HS → List ℤ) (zs : List GI) (l : List ℤ) (xs : List (Fin r → ℂ)) (hx : RecRep r p zs xs) (hl : xs.length = vol (Butterfly.layerShape P K D S)) (h0 : f 0 = gflat zs ++ l) (hC : ClN f) (hb : GB w zs) (hdisk : ∀ j (h : j < xs.length), ‖xs[j]‖ ≤ 1) : ∃ zs', RecRep r p zs' (Butterfly.prop14Proc (P := P) (S := S) hρ p (Butterfly.tens Butterfly.Cm : Butterfly.Op (Fin D)) xs) ∧ GB (p + 1) zs' ∧ (∀ j (h : j < (Butterfly.prop14Proc (P := P) (S := S) hρ p (Butterfly.tens Butterfly.Cm : Butterfly.Op (Fin D)) xs).length) (h' : j < (Butterfly.layerH P K D S ρ hρ xs).length), ∀ c, ‖(Butterfly.prop14Proc (P := P) (S := S) hρ p (Butterfly.tens Butterfly.Cm : Butterfly.Op (Fin D)) xs)[j] c - (Butterfly.layerH P K D S ρ hρ xs)[j] c‖ < Real.sqrt 2 * 2⁻¹ ^ p) ∧ IRuns Isym iprog (p14Ph P K D S ρ r E dC Cc w) (encK s f) (encK s (Function.update f 0 (gflat zs' ++ l))) (kC w + cWrapPh P K D S r E (zsz ((16 * (vol (Butterfly.layerShape P K D S) * r) : ℕ) : ℤ)) w dC) := by set N := vol (Butterfly.layerShape P K D S) * r set Z := zsz ((16 * N : ℕ) : ℤ) have hZ16 : zsz ((16 * N : ℕ) : ℤ) ≤ Z := le_rfl have hZ : zsz ((12 * N : ℕ) : ℤ) ≤ Z := le_trans (zsz_nat_le (by omega)) hZ16 have hsL : SLaws (fun i : Fin D => KFH.stT K D S ρ i) (vol (Butterfly.layerShape P K D S)) := slaws_of_strideSel (strideSel_layer (P := P) (D := D) (S := S) hρ) have L1 := (sImpl_SD (P := P) (K := K) (D := D) (S := S) (ρ := ρ) hρ hr hS hP Z hZ16).toI (I := Isym) (iprog := iprog) (fok_sdP _ _ _ _ _ _) have L4 := (sImpl_of_limpl hρ (limpl_ker (P := P) (S := S) hρ ⟨0, hD⟩ hr hS hP (M := MD D) ⟨Sm_gD D, Sm_zero, Sm_zero, Sm_gD D⟩ (kerOk_MD D) Z hZ)).toI (I := Isym) (iprog := iprog) (fok_kerP _ _ _ _ _ _ _ _) have L := ((L1.comp hsL hCimpl).comp hsL L1).comp hsL L4 obtain ⟨zs1, r1, b1, f1⟩ := L s f zs l xs p w hC h0 hx hl hb rw [← selOp_eq_selOpF (strideSel_layer hρ)] at r1 have hT : Butterfly.tensF (Butterfly.kerAt (⟨0, hD⟩ : Fin D) (Butterfly.cb ^ D • (1 : Butterfly.M2))) * (SD * (Butterfly.tens Butterfly.Cm * SD)) = (Butterfly.tens Butterfly.H0 : Butterfly.Op (Fin D)) := by rw [tensF_kerAt_smul_one, Butterfly.tens_H0, Fintype.card_fin, smul_mul_assoc, one_mul, mul_assoc] rw [hT] at r1 have r1' : RecRep r (p + (E + (D / 2 + D % 2))) zs1 (Butterfly.layerH P K D S ρ hρ xs) := by have e : p + (0 + E + 0 + (D / 2 + D % 2)) = p + (E + (D / 2 + D % 2)) := by ring rw [e] at r1; exact r1 have hz1 : zs1.length = N := by rw [r1'.1, Butterfly.layerH, Butterfly.butterflyLayer, Butterfly.length_selOp] obtain ⟨rT, bT, fT⟩ := truncP_rec s (Function.update f 0 (gflat zs1 ++ l)) zs1 _ l r1' (by simp) (hC.upd0 _).cl (w := w + dC + 2) (b1.mono (by omega)) Z (by rw [hz1]; exact zsz_natCast_le' (by omega)) obtain ⟨hout, hdisk', herr⟩ := Butterfly.prop14_output (P := P) (S := S) hρ p (Butterfly.tens Butterfly.Cm) rfl xs hdisk rw [← hout] at rT refine ⟨_, rT, GB_trunc_disk rT (fun j hj c => hdisk' j hj c), herr, ?_⟩ have F := f1.seq (fT.irun (I := Isym) (iprog := iprog) (fok_truncP _ _)) rw [Function.update_idem, hz1] at F refine F.mono (le_of_eq ?_) simp only [cWrapPh, cSD, Nat.add_zero, Nat.zero_add] ring  end Wrap  /-! ## 3. The wrapper cost has no factor `D` on the data
--
--   The following holds (Lean statement, in the scope of module `Solutions.KFMPhase`):
--
--   ```lean
--   theorem NLogN.KFM.cWrapPh_le (P K D S r E Z w dC : ℕ) :
--       cWrapPh P K D S r E Z w dC ≤
--         1000000 * (w + dC + E + D + 10) * (vol (Butterfly.layerShape P K D S) * r) +
--           1000000 * (K * D + P + 10) * (Z + 2)
--   ```
--
--   **Context.** The lemma belongs to the part *KFM 2: Proposition 14 with the phase diagonals `S_D` in one pass each*: `KFN.p14WithI` implements `S_D = diag i^{x_1+⋯+x_D}` as `D` kernel passes (`kersP … MS`), so one
--   simultaneous butterfly round costs `Θ(D · N · w)` even before the `C`-layer.  Lemma 16 runs `≈ ℓ`
--   such rounds with `D ≈ d`, giving `ℓ d V ≈ V log T`: a full logarithmic factor, which `Ncost`
--   (`ℓ d^{λ'}` for this row) cannot absorb (MACHINE-PLAN.md, item 4, issue (A)).
--
--   **Formalization Note.** This lemma belongs to the item-language (IL) layer of the integer-multiplication-kappa campaign: tape-level programs (register programs over 64 item stacks of the `NLogN` multitape framework, definition bundles `IntMul_HvdH_M_Defs1`–`IntMul_HvdH_M_Defs8`) that implement the data-movement primitives of the OpenAI preprint *Integer multiplication below $n\log n$* (field moves, row split/merge, shifts, the uniform Proposition 11 interchange, Lemma 12 with fine $O(1)$-per-element costs, Gaussian record primitives, Proposition 14 pieces) with exact list denotations from the array-model bundles `IntMul_Kappa_K_Defs*` and explicit cost bounds. All names refer to the definition bundles up to `IntMul_Kappa_K_Defs20`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026. Lemma `NLogN.KFM.cWrapPh_le` of the Lean development Solutions/KFMPhase.lean (lines 177–192), integer-multiplication-kappa campaign.

-- OpenAI-preprint / κ-improvement development (integer-multiplication-kappa), generated by skeleton subtraction.

import Definitions.Def_IntMul_Kappa_K_Defs20

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open NLogN
open NLogN.KFM
open IntMul RS AModel KIL KFD KFB KFG KFH KFN Complex P8Lift Butterfly

theorem NLogN.KFM.cWrapPh_le (P K D S r E Z w dC : ℕ) :
    cWrapPh P K D S r E Z w dC ≤
      1000000 * (w + dC + E + D + 10) * (vol (Butterfly.layerShape P K D S) * r) +
        1000000 * (K * D + P + 10) * (Z + 2) := by sorry
