-- Prove2me | Theorems.Thm_NLogN_KFM_prop14Ph_kTable
-- name    : NLogN.KFM.prop14Ph_kTable
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-14T11:49:40.88683+00:00
-- url     : https://prove2.me/theorems/712db8bb-aa1c-47d9-a3fc-60bfd10ffe67
-- title:
--   Proposition 14 in IL, unconditional, in the merged table (λ = τ50)
-- statement:
--   **Proposition 14 in IL, unconditional, in the merged table** (`λ = τ50`).
--
--   The following holds (Lean statement, in the scope of module `Solutions.KFMTable`):
--
--   ```lean
--   theorem NLogN.KFM.prop14Ph_kTable (ext : Fin E → IStmt HS (7 + E)) : ∃ (A : ℕ) (Kc : ℝ), 0 < Kc ∧
--       ∀ (Isym : List Sym) {K r Z : ℕ}, 6 ≤ K → 1 ≤ r → 80 * Z * (Z + 2) ≤ 2 ^ K →
--       let CR : ℝ := Kc * (K + 2) + 1
--       let Ψ : ℕ → ℕ := KFR.PsiR r Z
--       ∀ {P D S ρ : ℕ} (hρ : ρ < K), 1 ≤ S → 1 ≤ P → 1 ≤ D →
--       zsz ((32 * (vol (Butterfly.layerShape P K D S) * r) : ℕ) : ℤ) ≤ Z →
--       ∃ (Cc : ℕ → IStmt HS (7 + E)) (E dC : ℕ) (kC : ℕ → ℕ),
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
--             IRuns Isym (kTable ext) (p14Ph P K D S ρ r E dC Cc w) (encK st f)
--               (encK st (Function.update f 0 (gflat zs' ++ l)))
--               (kC w + cWrapPh P K D S r E
--                 (zsz ((16 * (vol (Butterfly.layerShape P K D S) * r) : ℕ) : ℤ)) w dC)
--   ```
--
--   **Context.** The lemma belongs to the part *KFM 7: one procedure table for Lemma 12 / Prop 14 and the FM multiplier*: Procedure tables are merged by renaming procedure indices (`IStmt.ren id g`, nlogn `HRen`).
--
--   **Formalization Note.** This lemma belongs to the item-language (IL) layer of the integer-multiplication-kappa campaign: tape-level programs (register programs over 64 item stacks of the `NLogN` multitape framework, definition bundles `IntMul_HvdH_M_Defs1`–`IntMul_HvdH_M_Defs8`) that implement the data-movement primitives of the OpenAI preprint *Integer multiplication below $n\log n$* (field moves, row split/merge, shifts, the uniform Proposition 11 interchange, Lemma 12 with fine $O(1)$-per-element costs, Gaussian record primitives, Proposition 14 pieces) with exact list denotations from the array-model bundles `IntMul_Kappa_K_Defs*` and explicit cost bounds. All names refer to the definition bundles up to `IntMul_Kappa_K_Defs22`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026. Lemma `NLogN.KFM.prop14Ph_kTable` of the Lean development Solutions/KFMTable.lean (lines 130–179), integer-multiplication-kappa campaign.

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
variable {E : ℕ}

theorem NLogN.KFM.prop14Ph_kTable (ext : Fin E → IStmt HS (7 + E)) : ∃ (A : ℕ) (Kc : ℝ), 0 < Kc ∧
    ∀ (Isym : List Sym) {K r Z : ℕ}, 6 ≤ K → 1 ≤ r → 80 * Z * (Z + 2) ≤ 2 ^ K →
    let CR : ℝ := Kc * (K + 2) + 1
    let Ψ : ℕ → ℕ := KFR.PsiR r Z
    ∀ {P D S ρ : ℕ} (hρ : ρ < K), 1 ≤ S → 1 ≤ P → 1 ≤ D →
    zsz ((32 * (vol (Butterfly.layerShape P K D S) * r) : ℕ) : ℤ) ≤ Z →
    ∃ (Cc : ℕ → IStmt HS (7 + E)) (E dC : ℕ) (kC : ℕ → ℕ),
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
          IRuns Isym (kTable ext) (p14Ph P K D S ρ r E dC Cc w) (encK st f)
            (encK st (Function.update f 0 (gflat zs' ++ l)))
            (kC w + cWrapPh P K D S r E
              (zsz ((16 * (vol (Butterfly.layerShape P K D S) * r) : ℕ) : ℤ)) w dC) := by sorry
