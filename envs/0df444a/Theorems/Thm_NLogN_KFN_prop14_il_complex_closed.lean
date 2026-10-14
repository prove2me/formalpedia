-- Prove2me | Theorems.Thm_NLogN_KFN_prop14_il_complex_closed
-- name    : NLogN.KFN.prop14_il_complex_closed
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-14T05:27:47.964649+00:00
-- url     : https://prove2.me/theorems/8f8fc7c5-802c-4366-b85c-0c225fc1d984
-- title:
--   Proposition 14 in IL for complexIface, closed bounds
-- statement:
--   **Proposition 14 in IL for `complexIface`, closed bounds.**  With `m = 10^6`, `k = ⌊log_m D⌋`, `L` the number of steps of the network, `G = Gb L s_c W_c A`, `a = (s_c + L) alN + 1`, `b = (s_c + L) CR` and `λ = log_m max(s_c/W_c, m^τ, 1) < 1`: scale `E ≤ D + (k+1) m (k+1) G^k`, width `dC ≤ 2D + (k+1) m · 4 (k+1)^2 G^{k+2}`, and `C`-layer cost `kC w ≤ (2 ((k+1) m (10^5 + k a + 2 k b) D^λ + 1) + 10^6 (D+2)) · vol · Xf_r,Ψ(w + 2D + (k+1) m 4 (k+1)^2 G^{k+2} + 20 (k+1)^3 G^{k+2} + 2)`.
--
--   The following holds (Lean statement, in the scope of module `Solutions.KFNClosed`):
--
--   ```lean
--   theorem NLogN.KFN.prop14_il_complex_closed : ∃ (A : ℕ) (lam : ℝ), 0 ≤ lam ∧ lam < 1 ∧
--       ∀ {K r Z : ℕ} {Ψ : ℕ → ℕ} {CR : ℝ},
--       RowHyp Isym iprog K (100 ^ 3) r Z Ψ CR τ50 → 0 ≤ CR → 1 ≤ r → Monotone Ψ →
--       (∀ v, Z + 2 ≤ Ψ v) → ∀ {P D S ρ : ℕ} (hρ : ρ < K), 1 ≤ S → 1 ≤ P → 1 ≤ D →
--       zsz ((32 * (vol (Butterfly.layerShape P K D S) * r) : ℕ) : ℤ) ≤ Z →
--       ∃ (Cc : ℕ → IStmt HS Pp) (E dC : ℕ) (kC : ℕ → ℕ),
--         E ≤ D + (Nat.log (100 ^ 3) D + 1) * 100 ^ 3 * ((Nat.log (100 ^ 3) D + 1) *
--           NLogN.KFN.Gb P8Lift.complexIface.net.length P8Lift.sc P8Lift.Wc A ^ Nat.log (100 ^ 3) D) ∧
--         dC ≤ 2 * D + (Nat.log (100 ^ 3) D + 1) * 100 ^ 3 * (4 * (Nat.log (100 ^ 3) D + 1) ^ 2 *
--           NLogN.KFN.Gb P8Lift.complexIface.net.length P8Lift.sc P8Lift.Wc A ^ (Nat.log (100 ^ 3) D + 2)) ∧
--         (∀ w, (kC w : ℝ) ≤ (2 * ((((Nat.log (100 ^ 3) D + 1) * 100 ^ 3 : ℕ) : ℝ) *
--             ((100000 + (Nat.log (100 ^ 3) D : ℝ) *
--               (((P8Lift.sc + P8Lift.complexIface.net.length) * alN P8Lift.Wc A + 1 : ℕ) : ℝ) +
--               (Nat.log (100 ^ 3) D : ℝ) *
--                 (2 * (((P8Lift.sc + P8Lift.complexIface.net.length : ℕ) : ℝ) * CR))) *
--               (D : ℝ) ^ lam) + 1) + 1000000 * ((D : ℝ) + 2)) *
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
--             IRuns Isym iprog (p14WithI P K D S ρ r E Cc w) (encK st f)
--               (encK st (Function.update f 0 (gflat zs' ++ l)))
--               (kC (w + 2 * D) + cWrapE D E (vol (Butterfly.layerShape P K D S) * r)
--                 (zsz ((12 * (vol (Butterfly.layerShape P K D S) * r) : ℕ) : ℤ)) w dC)
--   ```
--
--   **Context.** The lemma belongs to the part *KFN: closed bounds for the recursion constants*.
--
--   **Formalization Note.** This lemma belongs to the item-language (IL) layer of the integer-multiplication-kappa campaign: tape-level programs (register programs over 64 item stacks of the `NLogN` multitape framework, definition bundles `IntMul_HvdH_M_Defs1`–`IntMul_HvdH_M_Defs8`) that implement the data-movement primitives of the OpenAI preprint *Integer multiplication below $n\log n$* (field moves, row split/merge, shifts, the uniform Proposition 11 interchange, Lemma 12 with fine $O(1)$-per-element costs, Gaussian record primitives, Proposition 14 pieces) with exact list denotations from the array-model bundles `IntMul_Kappa_K_Defs*` and explicit cost bounds. All names refer to the definition bundles up to `IntMul_Kappa_K_Defs20`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026. Lemma `NLogN.KFN.prop14_il_complex_closed` of the Lean development Solutions/KFNClosed.lean (lines 309–401), integer-multiplication-kappa campaign.

-- OpenAI-preprint / κ-improvement development (integer-multiplication-kappa), generated by skeleton subtraction.

import Definitions.Def_IntMul_Kappa_K_Defs20

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open NLogN
open NLogN.KFN
open IntMul RS AModel KIL KFD KFB KFG KFH Complex P8Lift Butterfly
variable {Pp : ℕ} {Isym : List Sym} {iprog : Fin Pp → IStmt HS Pp}

theorem NLogN.KFN.prop14_il_complex_closed : ∃ (A : ℕ) (lam : ℝ), 0 ≤ lam ∧ lam < 1 ∧
    ∀ {K r Z : ℕ} {Ψ : ℕ → ℕ} {CR : ℝ},
    RowHyp Isym iprog K (100 ^ 3) r Z Ψ CR τ50 → 0 ≤ CR → 1 ≤ r → Monotone Ψ →
    (∀ v, Z + 2 ≤ Ψ v) → ∀ {P D S ρ : ℕ} (hρ : ρ < K), 1 ≤ S → 1 ≤ P → 1 ≤ D →
    zsz ((32 * (vol (Butterfly.layerShape P K D S) * r) : ℕ) : ℤ) ≤ Z →
    ∃ (Cc : ℕ → IStmt HS Pp) (E dC : ℕ) (kC : ℕ → ℕ),
      E ≤ D + (Nat.log (100 ^ 3) D + 1) * 100 ^ 3 * ((Nat.log (100 ^ 3) D + 1) *
        NLogN.KFN.Gb P8Lift.complexIface.net.length P8Lift.sc P8Lift.Wc A ^ Nat.log (100 ^ 3) D) ∧
      dC ≤ 2 * D + (Nat.log (100 ^ 3) D + 1) * 100 ^ 3 * (4 * (Nat.log (100 ^ 3) D + 1) ^ 2 *
        NLogN.KFN.Gb P8Lift.complexIface.net.length P8Lift.sc P8Lift.Wc A ^ (Nat.log (100 ^ 3) D + 2)) ∧
      (∀ w, (kC w : ℝ) ≤ (2 * ((((Nat.log (100 ^ 3) D + 1) * 100 ^ 3 : ℕ) : ℝ) *
          ((100000 + (Nat.log (100 ^ 3) D : ℝ) *
            (((P8Lift.sc + P8Lift.complexIface.net.length) * alN P8Lift.Wc A + 1 : ℕ) : ℝ) +
            (Nat.log (100 ^ 3) D : ℝ) *
              (2 * (((P8Lift.sc + P8Lift.complexIface.net.length : ℕ) : ℝ) * CR))) *
            (D : ℝ) ^ lam) + 1) + 1000000 * ((D : ℝ) + 2)) *
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
          IRuns Isym iprog (p14WithI P K D S ρ r E Cc w) (encK st f)
            (encK st (Function.update f 0 (gflat zs' ++ l)))
            (kC (w + 2 * D) + cWrapE D E (vol (Butterfly.layerShape P K D S) * r)
              (zsz ((12 * (vol (Butterfly.layerShape P K D S) * r) : ℕ) : ℤ)) w dC) := by sorry
