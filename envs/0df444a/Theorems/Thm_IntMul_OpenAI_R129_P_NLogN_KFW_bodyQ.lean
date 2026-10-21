-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFW_bodyQ
-- name    : IntMul.OpenAI.R129.P.NLogN.KFW.bodyQ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:12.076503+00:00
-- url     : https://prove2.me/theorems/cb58b96b-bd06-4fb0-aa93-b6603c8cd187
-- title:
--   The layer body (κ = 2⁻¹²⁹ constants)
-- statement:
--   **The layer body**, at the `same-network-129` constants.
--
--   This is `NLogN.KFW.bodyQ` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFW C-layer 10: the layer body `S_D ; C ; S_D ; b^D ; Q_p`*: With the core registers and the total scale `E = q₀ + lowF ES k D' + ⌊D/2⌋ + D mod 2` on
--   register `24`, the fixed code `bodyC jT jW` runs the uniform `S_D` (`sdC`), the `C`-layer
--   (`clC`), `S_D`, the scalar `b^D` (`mdC`), and the truncation `truncU 17 18` (frame
--   `17 = 2^E`, `18 = 2 N`).
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFW.bodyQ` (https://prove2.me/theorems/65a2227a-81ee-41bb-bbe1-5ab76436221f).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open _root_.NLogN hiding padL vE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFW hiding RowU RowUP cBody cCL cChain cLowP cLowPart cTot cbW clF coefF
open _root_.IntMul.OpenAI.R129.P.NLogN.KFW
open Complex
open _root_.IntMul
open _root_.NLogN.RS
open _root_.NLogN.KFW.RS
open _root_.AModel hiding hdPos logStep stepC
open _root_.NLogN.KIL hiding Cfg FR FrOK St aE bodyU cBody fIn kS negP outR pT padL rowR stD
open _root_.NLogN.KFD hiding levF scr
open _root_.NLogN.KFB hiding permL permP
open _root_.NLogN.KFG hiding cTbl imE reE xD
open _root_.NLogN.KFH
open _root_.NLogN.KFN hiding pcs phStepC τ50
open _root_.IntMul.OpenAI.R129.P.NLogN.KFN
open _root_.P8Lift
open _root_.Butterfly hiding Op
variable {Pp : ℕ} {Isym : List Sym} {tbl : Fin Pp → IStmt HS Pp}

open _root_.NLogN hiding padL vE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFW hiding RowU RowUP cBody cCL cChain cLowP cLowPart cTot cbW clF coefF
open _root_.IntMul.OpenAI.R129.P.NLogN.KFW

theorem IntMul.OpenAI.R129.P.NLogN.KFW.bodyQ (jT jL jW : Fin Pp) (rowC : IStmt HS Pp) (hT : tbl jT = NLogN.KFW.topC jT jL)
    (hW : tbl jW = lowC jW jL) (hL : tbl jL = levC jL rowC)
    {K S r H P D ρ k q0 Bp Z Zr Mb Bz : ℕ} {Kc : ℝ}
    (LV : ∀ j, LvQ Isym tbl jL rowC K r Z Zr H j (cbW Kc K j))
    (hρ : ρ < K) (hS : 1 ≤ S) (hP : 1 ≤ P) (hr : 1 ≤ r) (hD : 1 ≤ D) (hq : q0 ≤ D)
    (hZ16 : zsz ((16 * (P * 2 ^ (K * D) * S * r) : ℕ) : ℤ) ≤ Z)
    (hV : zsz ((Vb K (K * D) S r H 0 P : ℕ) : ℤ) ≤ Zr)
    (hMb : zsz (Mb : ℤ) ≤ Bz) (hM : K * D + P + 10 ≤ Mb)
    (pre : q0 < D → LowPre K S r H P D ρ k q0 Bp Z Zr Mb Bz)
    (hEZ : zsz (((q0 + lowF ES k (D - q0) + (D / 2 + D % 2)) : ℕ) : ℤ) ≤ Z)
    {σ : Fin HS → Option ℤ} (hC : CoreR σ K S r H P D ρ k q0 Bp)
    (hE : σ 24 = some (((q0 + lowF ES k (D - q0) + (D / 2 + D % 2)) : ℕ) : ℤ))
    (f : Fin HS → List ℤ) (zs : List GI) (l : List ℤ) (xs : List (Fin r → ℂ)) (p w : ℕ)
    (hC0 : Clean0 f) (h0 : f 0 = gflat zs ++ l) (hx : RecRep r p zs xs)
    (hl : xs.length = vol (Butterfly.layerShape P K D S)) (hb : NLogN.KFB.GB w zs)
    (hH : w + (2 * q0 + lowF DWl k (D - q0) + 2) ≤ H)
    (hdisk : ∀ j (h : j < xs.length), ‖xs[j]‖ ≤ 1) :
    ∃ zs', RecRep r p zs' (Butterfly.prop14Proc (P := P) (S := S) hρ p
        (Butterfly.tens Butterfly.Cm : Butterfly.Op (Fin D)) xs) ∧
      NLogN.KFB.GB (p + 1) zs' ∧
      (∀ j (h : j < (Butterfly.prop14Proc (P := P) (S := S) hρ p
          (Butterfly.tens Butterfly.Cm : Butterfly.Op (Fin D)) xs).length)
        (h' : j < (Butterfly.layerH P K D S ρ hρ xs).length), ∀ c,
        ‖(Butterfly.prop14Proc (P := P) (S := S) hρ p
          (Butterfly.tens Butterfly.Cm : Butterfly.Op (Fin D)) xs)[j] c -
          (Butterfly.layerH P K D S ρ hρ xs)[j] c‖ < Real.sqrt 2 * 2⁻¹ ^ p) ∧
      RunQ Isym tbl σ (NLogN.KFW.bodyC jT jW) f (Function.update f 0 (gflat zs' ++ l))
        (IntMul.OpenAI.R129.P.NLogN.KFW.cBody Kc K S r H P D k q0 Bp Z Zr Bz w) := by sorry
