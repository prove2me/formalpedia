-- Prove2me | Theorems.Thm_NLogN_KFM_prop14Ph_l12
-- name    : NLogN.KFM.prop14Ph_l12
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-14T11:53:47.766308+00:00
-- url     : https://prove2.me/theorems/47004b9b-997e-444c-aba7-da0791546eba
-- title:
--   Proposition 14 in IL, unconditional: for the Lemma 12 table KFL.l12prog, with λ = τ50, CR = Kc (K+2) + 1…
-- statement:
--   **Proposition 14 in IL, unconditional**: for the Lemma 12 table `KFL.l12prog`, with `λ = τ50`, `CR = Kc (K+2) + 1` and `Ψ = PsiR r Z`.
--
--   The following holds (Lean statement, in the scope of module `Solutions.KFMProp14U`):
--
--   ```lean
--   theorem NLogN.KFM.prop14Ph_l12 : ∃ (A : ℕ) (Kc : ℝ), 0 < Kc ∧
--       ∀ (Isym : List Sym) {K r Z : ℕ}, 6 ≤ K → 1 ≤ r → 80 * Z * (Z + 2) ≤ 2 ^ K →
--       let CR : ℝ := Kc * (K + 2) + 1
--       let Ψ : ℕ → ℕ := KFR.PsiR r Z
--       ∀ {P D S ρ : ℕ} (hρ : ρ < K), 1 ≤ S → 1 ≤ P → 1 ≤ D →
--       zsz ((32 * (vol (Butterfly.layerShape P K D S) * r) : ℕ) : ℤ) ≤ Z →
--       ∃ (Cc : ℕ → IStmt HS 1) (E dC : ℕ) (kC : ℕ → ℕ),
--         E ≤ D + (Nat.log (100 ^ 3) D + 1) * 100 ^ 3 * ((Nat.log (100 ^ 3) D + 1) *
--           NLogN.KFN.Gb P8Lift.complexIface.net.length P8Lift.sc P8Lift.Wc A ^ Nat.log (100 ^ 3) D) ∧
--         dC ≤ 2 * D + (Nat.log (100 ^ 3) D + 1) * 100 ^ 3 * (4 * (Nat.log (100 ^ 3) D + 1) ^ 2 *
--           NLogN.KFN.Gb P8Lift.complexIface.net.length P8Lift.sc P8Lift.Wc A ^ (Nat.log (100 ^ 3) D + 2)) ∧
--         (∀ w, (kC w : ℝ) ≤ (2 * ((((Nat.log (100 ^ 3) D + 1) * 100 ^ 3 : ℕ) : ℝ) *
--             ((100000 + (Nat.log (100 ^ 3) D : ℝ) *
--               (((P8Lift.sc + P8Lift.complexIface.net.length) * alN P8Lift.Wc A + 1 : ℕ) : ℝ) +
--               (Nat.log (100 ^ 3) D : ℝ) *
--                 (2 * (((P8Lift.sc + P8Lift.complexIface.net.length : ℕ) : ℝ) * CR))) *
--               (D : ℝ) ^ τ50) + 1) + 1000000 * (((Nat.log (100 ^ 3) D * 71 : ℕ) : ℝ) + 2)) *
--           ((vol (Butterfly.layerShape P K D S) : ℕ) : ℝ) *
--           (Xf r Ψ (w + 2 * D + (Nat.log (100 ^ 3) D + 1) * 100 ^ 3 *
--             (4 * (Nat.log (100 ^ 3) D + 1) ^ 2 *
--               NLogN.KFN.Gb P8Lift.complexIface.net.length P8Lift.sc P8Lift.Wc A ^ (Nat.log (100 ^ 3) D + 2)) +
--             20 * (Nat.log (100 ^ 3) D + 1) ^ 3 *
--               NLogN.KFN.Gb P8Lift.complexIface.net.length P8Lift.sc P8Lift.Wc A ^ (Nat.log (100 ^ 3) D + 2) +
--             2) : ℝ)) ∧
--         ∀ (st : IState HS) (f : Fin HS → List ℤ) (zs : List GI) (l : List ℤ)
--           (xs : List (Fin r → ℂ)) (p w : ℕ), RecRep r p zs xs →
--           xs.length = vol (Butterfly.layerShape P K D S) → f 0 = gflat zs ++ l → ClN f →
--           NLogN.KFB.GB w zs → (∀ j (h : j < xs.length), ‖xs[j]‖ ≤ 1) →
--           ∃ zs', RecRep r p zs' (Butterfly.prop14Proc (P := P) (S := S) hρ p
--               (Butterfly.tens Butterfly.Cm : Butterfly.Op (Fin D)) xs) ∧
--             NLogN.KFB.GB (p + 1) zs' ∧
--             (∀ j (h : j < (Butterfly.prop14Proc (P := P) (S := S) hρ p
--                 (Butterfly.tens Butterfly.Cm : Butterfly.Op (Fin D)) xs).length)
--               (h' : j < (Butterfly.layerH P K D S ρ hρ xs).length), ∀ c,
--               ‖(Butterfly.prop14Proc (P := P) (S := S) hρ p
--                 (Butterfly.tens Butterfly.Cm : Butterfly.Op (Fin D)) xs)[j] c -
--                 (Butterfly.layerH P K D S ρ hρ xs)[j] c‖ < Real.sqrt 2 * 2⁻¹ ^ p) ∧
--             IRuns Isym KFL.l12prog (p14Ph P K D S ρ r E dC Cc w) (encK st f)
--               (encK st (Function.update f 0 (gflat zs' ++ l)))
--               (kC w + cWrapPh P K D S r E
--                 (zsz ((16 * (vol (Butterfly.layerShape P K D S) * r) : ℕ) : ℤ)) w dC)
--   ```
--
--   **Context.** The lemma belongs to the part *KFM 4b: Proposition 14 (one-pass phases) for the Lemma 12 table, unconditional*: `KFMProp14.prop14Ph_complex_closed` with its `RowHyp` hypothesis discharged by
--   `KFR.closedHyps_uncond` (KFL's proof of Lemma 13 in IL, for the table `KFL.l12prog`), with
--   `CR = Kc (K+2) + 1`, `Ψ = KFR.PsiR r Z`, and the exponent `λ = τ50` (`KFMLam.lam_complex_eq`).
--   The gate-class constant `A` is chosen once, before `Isym`, `K`, `r`, `Z`.
--   The only side conditions left are `6 ≤ K`, `1 ≤ r` and `80 Z (Z+2) ≤ 2^K`.
--
--   **Formalization Note.** This lemma belongs to the item-language (IL) layer of the integer-multiplication-kappa campaign: tape-level programs (register programs over 64 item stacks of the `NLogN` multitape framework, definition bundles `IntMul_HvdH_M_Defs1`–`IntMul_HvdH_M_Defs8`) that implement the data-movement primitives of the OpenAI preprint *Integer multiplication below $n\log n$* (field moves, row split/merge, shifts, the uniform Proposition 11 interchange, Lemma 12 with fine $O(1)$-per-element costs, Gaussian record primitives, Proposition 14 pieces) with exact list denotations from the array-model bundles `IntMul_Kappa_K_Defs*` and explicit cost bounds. All names refer to the definition bundles up to `IntMul_Kappa_K_Defs22`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026. Lemma `NLogN.KFM.prop14Ph_l12` of the Lean development Solutions/KFMProp14U.lean (lines 120–170), integer-multiplication-kappa campaign.

-- OpenAI-preprint / κ-improvement development (integer-multiplication-kappa), generated by skeleton subtraction.

import Definitions.Def_IntMul_Kappa_K_Defs22

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open NLogN
open NLogN.KFM
open IntMul RS AModel KIL KFD KFB KFG KFH KFN Complex P8Lift Butterfly

theorem NLogN.KFM.prop14Ph_l12 : ∃ (A : ℕ) (Kc : ℝ), 0 < Kc ∧
    ∀ (Isym : List Sym) {K r Z : ℕ}, 6 ≤ K → 1 ≤ r → 80 * Z * (Z + 2) ≤ 2 ^ K →
    let CR : ℝ := Kc * (K + 2) + 1
    let Ψ : ℕ → ℕ := KFR.PsiR r Z
    ∀ {P D S ρ : ℕ} (hρ : ρ < K), 1 ≤ S → 1 ≤ P → 1 ≤ D →
    zsz ((32 * (vol (Butterfly.layerShape P K D S) * r) : ℕ) : ℤ) ≤ Z →
    ∃ (Cc : ℕ → IStmt HS 1) (E dC : ℕ) (kC : ℕ → ℕ),
      E ≤ D + (Nat.log (100 ^ 3) D + 1) * 100 ^ 3 * ((Nat.log (100 ^ 3) D + 1) *
        NLogN.KFN.Gb P8Lift.complexIface.net.length P8Lift.sc P8Lift.Wc A ^ Nat.log (100 ^ 3) D) ∧
      dC ≤ 2 * D + (Nat.log (100 ^ 3) D + 1) * 100 ^ 3 * (4 * (Nat.log (100 ^ 3) D + 1) ^ 2 *
        NLogN.KFN.Gb P8Lift.complexIface.net.length P8Lift.sc P8Lift.Wc A ^ (Nat.log (100 ^ 3) D + 2)) ∧
      (∀ w, (kC w : ℝ) ≤ (2 * ((((Nat.log (100 ^ 3) D + 1) * 100 ^ 3 : ℕ) : ℝ) *
          ((100000 + (Nat.log (100 ^ 3) D : ℝ) *
            (((P8Lift.sc + P8Lift.complexIface.net.length) * alN P8Lift.Wc A + 1 : ℕ) : ℝ) +
            (Nat.log (100 ^ 3) D : ℝ) *
              (2 * (((P8Lift.sc + P8Lift.complexIface.net.length : ℕ) : ℝ) * CR))) *
            (D : ℝ) ^ τ50) + 1) + 1000000 * (((Nat.log (100 ^ 3) D * 71 : ℕ) : ℝ) + 2)) *
        ((vol (Butterfly.layerShape P K D S) : ℕ) : ℝ) *
        (Xf r Ψ (w + 2 * D + (Nat.log (100 ^ 3) D + 1) * 100 ^ 3 *
          (4 * (Nat.log (100 ^ 3) D + 1) ^ 2 *
            NLogN.KFN.Gb P8Lift.complexIface.net.length P8Lift.sc P8Lift.Wc A ^ (Nat.log (100 ^ 3) D + 2)) +
          20 * (Nat.log (100 ^ 3) D + 1) ^ 3 *
            NLogN.KFN.Gb P8Lift.complexIface.net.length P8Lift.sc P8Lift.Wc A ^ (Nat.log (100 ^ 3) D + 2) +
          2) : ℝ)) ∧
      ∀ (st : IState HS) (f : Fin HS → List ℤ) (zs : List GI) (l : List ℤ)
        (xs : List (Fin r → ℂ)) (p w : ℕ), RecRep r p zs xs →
        xs.length = vol (Butterfly.layerShape P K D S) → f 0 = gflat zs ++ l → ClN f →
        NLogN.KFB.GB w zs → (∀ j (h : j < xs.length), ‖xs[j]‖ ≤ 1) →
        ∃ zs', RecRep r p zs' (Butterfly.prop14Proc (P := P) (S := S) hρ p
            (Butterfly.tens Butterfly.Cm : Butterfly.Op (Fin D)) xs) ∧
          NLogN.KFB.GB (p + 1) zs' ∧
          (∀ j (h : j < (Butterfly.prop14Proc (P := P) (S := S) hρ p
              (Butterfly.tens Butterfly.Cm : Butterfly.Op (Fin D)) xs).length)
            (h' : j < (Butterfly.layerH P K D S ρ hρ xs).length), ∀ c,
            ‖(Butterfly.prop14Proc (P := P) (S := S) hρ p
              (Butterfly.tens Butterfly.Cm : Butterfly.Op (Fin D)) xs)[j] c -
              (Butterfly.layerH P K D S ρ hρ xs)[j] c‖ < Real.sqrt 2 * 2⁻¹ ^ p) ∧
          IRuns Isym KFL.l12prog (p14Ph P K D S ρ r E dC Cc w) (encK st f)
            (encK st (Function.update f 0 (gflat zs' ++ l)))
            (kC w + cWrapPh P K D S r E
              (zsz ((16 * (vol (Butterfly.layerShape P K D S) * r) : ℕ) : ℤ)) w dC) := by sorry
