-- Prove2me | Theorems.Thm_NLogN_KFL_bits_permRecs
-- name    : NLogN.KFL.bits_permRecs
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-14T11:43:24.071495+00:00
-- url     : https://prove2.me/theorems/292f2d22-60aa-485e-a13b-8dabc294b202
-- title:
--   Slot py gets y ⊕ (x ∧ selM f), x = slot px. -/ def Fpp (K ρ f : ℕ) (px py : Fin 3) (c : Tr) : Tr := slotS…
-- statement:
--   Slot `py` gets `y ⊕ (x ∧ selM f)`, `x` = slot `px`. -/ def Fpp (K ρ f : ℕ) (px py : Fin 3) (c : Tr) : Tr := slotS c py (slotG c py ^^^ (slotG c px &&& selM K ρ f))  theorem slotG_lt {Q : ℕ} {c : Tr} (h : TV Q c) (t : Fin 3) : slotG c t < Q := by fin_cases t · exact h.1 · exact h.2.1 · exact h.2.2  theorem TV_slotS {Q : ℕ} {c : Tr} (h : TV Q c) (t : Fin 3) {v : ℕ} (hv : v < Q) : TV Q (slotS c t v) := by fin_cases t · exact ⟨hv, h.2.1, h.2.2⟩ · exact ⟨h.1, hv, h.2.2⟩ · exact ⟨h.1, h.2.1, hv⟩  theorem TV_Fpp {K ρ f L : ℕ} (px py : Fin 3) (c : Tr) (hc : TV (2 ^ L) c) : TV (2 ^ L) (Fpp K ρ f px py c) := by apply TV_slotS hc apply Nat.xor_lt_two_pow (slotG_lt hc py) exact lt_of_le_of_lt Nat.and_le_left (slotG_lt hc px)  theorem phi_slotS {g : Geo} (hg : g.Pos) {F : Tr → Tr} (hF : ∀ c, TV g.Q c → TV g.Q (F c)) (t : Fin 3) (v : Tr → ℕ) (hFv : ∀ c, F c = slotS c t (v c)) (n : ℕ) : (phi g F n : ℤ) = n + ((v (trOf g n) : ℤ) - slotG (trOf g n) t) * strd g t := by rw [phi_int hg hF, hFv] fin_cases t <;> simp [slotS, slotG, strd]  theorem phi_Fpp {N0 N1 N2 N3 K ρ f R w : ℕ} (h0 : 1 ≤ N0) (h1 : 1 ≤ N1) (h2 : 1 ≤ N2) (h3 : 1 ≤ N3) (hR : 1 ≤ R) (px py : Fin 3) {q : ℕ} (hq : q < vol (rect N0 N1 N2 N3 (f * K))) : phi (geoB N0 N1 N2 N3 (f * K) R w).recG (Fpp K ρ f px py) q = encode (rect N0 N1 N2 N3 (f * K)) (rowAddAddr K ρ f px py (decode (rect N0 N1 N2 N3 (f * K)) q)) := by set g := geoB N0 N1 N2 N3 (f * K) R w have hg : g.Pos := geoB_pos h0 h1 h2 h3 hR have hF : ∀ c, TV g.recG.Q c → TV g.recG.Q (Fpp K ρ f px py c) := fun c hc => TV_Fpp px py c hc have e1 := phi_slotS hg.recG hF py (fun c => slotG c py ^^^ (slotG c px &&& selM K ρ f)) (fun c => rfl) q have hl : (decode (rect N0 N1 N2 N3 (f * K)) q).length = 7 := by rw [length_decode]; rfl have e2 := KFH.encode_set (rect N0 N1 N2 N3 (f * K)) (decode (rect N0 N1 N2 N3 (f * K)) q) (slotF py) ((decode (rect N0 N1 N2 N3 (f * K)) q).getD (slotF py) 0 ^^^ ((decode (rect N0 N1 N2 N3 (f * K)) q).getD (slotF px) 0 &&& selMask K ρ f)) (by rw [hl]; fin_cases py <;> simp [slotF]) (by rw [hl]; rfl) rw [encode_decode hq, dig_slot (R := R) (w := w) hq, dig_slot (R := R) (w := w) hq, vol_slot (R := R) (w := w)] at e2 have : (phi g.recG (Fpp K ρ f px py) q : ℤ) = (encode (rect N0 N1 N2 N3 (f * K)) (rowAddAddr K ρ f px py (decode (rect N0 N1 N2 N3 (f * K)) q)) : ℤ) := by rw [e1]; unfold rowAddAddr rw [dig_slot (R := R) (w := w) hq, dig_slot (R := R) (w := w) hq, e2]; rfl exact_mod_cast this  /-! ## Records permuted by `rowAddAddr`, in bits
--
--   The following holds (Lean statement, in the scope of module `Solutions.KFLAddr`):
--
--   ```lean
--   theorem NLogN.KFL.bits_permRecs {N0 N1 N2 N3 K ρ f R w : ℕ} (h0 : 1 ≤ N0) (h1 : 1 ≤ N1) (h2 : 1 ≤ N2)
--       (h3 : 1 ≤ N3) (hR : 1 ≤ R) (px py : Fin 3) (zs : List GI)
--       (hl : zs.length = vol (rect N0 N1 N2 N3 (f * K)) * R) :
--       bitsL w (gflat (permRecs (rect N0 N1 N2 N3 (f * K)) (rowAddAddr K ρ f px py) R zs)) =
--         rixT (geoB N0 N1 N2 N3 (f * K) R w) (Fpp K ρ f px py) (bitsL w (gflat zs))
--   ```
--
--   **Context.** The lemma belongs to the part *KFL §17: `permRecs (rowAddAddr …)` as a triple map on the bit array*: The Gaussian records (`R` entries, `2 (w+1)` bits per entry after `toBitsI`) of the rectangle
--   `rect N0 N1 N2 N3 L` form the bit array of the geometry `geoB` (`Q = 2^L`, `B = 2 R (w+1)`).
--   `bits_permRecs`: converting `permRecs rect (rowAddAddr px py) R zs` to bits gives
--   `rixT (geoB …) (Fpp px py)` of the bits of `zs`, where `Fpp px py` replaces slot `py` by
--   `y ⊕ (x ∧ selM f)` (`x` = slot `px`).  `Fpp_conj`: `Fpp px py` is the canonical row addition
--   `RAc` conjugated by at most two slot swaps.
--
--   **Formalization Note.** This lemma belongs to the item-language (IL) layer of the integer-multiplication-kappa campaign: tape-level programs (register programs over 64 item stacks of the `NLogN` multitape framework, definition bundles `IntMul_HvdH_M_Defs1`–`IntMul_HvdH_M_Defs8`) that implement the data-movement primitives of the OpenAI preprint *Integer multiplication below $n\log n$* (field moves, row split/merge, shifts, the uniform Proposition 11 interchange, Lemma 12 with fine $O(1)$-per-element costs, Gaussian record primitives, Proposition 14 pieces) with exact list denotations from the array-model bundles `IntMul_Kappa_K_Defs*` and explicit cost bounds. All names refer to the definition bundles up to `IntMul_Kappa_K_Defs22`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026. Lemma `NLogN.KFL.bits_permRecs` of the Lean development Solutions/KFLAddr.lean (lines 193–213), integer-multiplication-kappa campaign.

-- OpenAI-preprint / κ-improvement development (integer-multiplication-kappa), generated by skeleton subtraction.

import Definitions.Def_IntMul_Kappa_K_Defs22

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open NLogN
open NLogN.KFL
open IntMul RS KIL KFD KFB KFH AModel Butterfly

theorem NLogN.KFL.bits_permRecs {N0 N1 N2 N3 K ρ f R w : ℕ} (h0 : 1 ≤ N0) (h1 : 1 ≤ N1) (h2 : 1 ≤ N2)
    (h3 : 1 ≤ N3) (hR : 1 ≤ R) (px py : Fin 3) (zs : List GI)
    (hl : zs.length = vol (rect N0 N1 N2 N3 (f * K)) * R) :
    bitsL w (gflat (permRecs (rect N0 N1 N2 N3 (f * K)) (rowAddAddr K ρ f px py) R zs)) =
      rixT (geoB N0 N1 N2 N3 (f * K) R w) (Fpp K ρ f px py) (bitsL w (gflat zs)) := by sorry
