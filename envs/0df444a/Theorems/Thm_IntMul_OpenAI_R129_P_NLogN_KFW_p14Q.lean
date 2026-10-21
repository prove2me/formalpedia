-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFW_p14Q
-- name    : IntMul.OpenAI.R129.P.NLogN.KFW.p14Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:25.060997+00:00
-- url     : https://prove2.me/theorems/90e49433-e065-4744-b3d9-89e568a87b50
-- title:
--   The entry procedure (κ = 2⁻¹²⁹ constants)
-- statement:
--   **The entry procedure**, at the `same-network-129` constants.
--
--   This is `NLogN.KFW.p14Q` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFW C-layer 16: the run of the entry procedure*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFW.p14Q` (https://prove2.me/theorems/987a5bcf-1dee-400d-be97-e2f4a66c2e4b).

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
open _root_.NLogN.KIL hiding Cfg FR FrOK St aE bodyU cBody fIn kS negP outR pT padL rowR stD
open _root_.NLogN.KFD hiding levF scr
open _root_.NLogN.KFB hiding permL permP
open _root_.NLogN.KFG hiding cTbl imE reE xD
open _root_.NLogN.KFH
open _root_.NLogN.KFN hiding pcs phStepC τ50
open _root_.IntMul.OpenAI.R129.P.NLogN.KFN
open _root_.Butterfly hiding Op
variable {Pp : ℕ} {Isym : List Sym} {tbl : Fin Pp → IStmt HS Pp}

open _root_.NLogN hiding padL vE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFW hiding RowU RowUP cBody cCL cChain cLowP cLowPart cTot cbW clF coefF
open _root_.IntMul.OpenAI.R129.P.NLogN.KFW

theorem IntMul.OpenAI.R129.P.NLogN.KFW.p14Q (jG jE jT jL jW : Fin Pp) (rowC : IStmt HS Pp)
    (hG : tbl jG = logC jG (coreC jE)) (hEc : tbl jE = eaccC jE (NLogN.KFW.bodyC jT jW))
    (hT : tbl jT = NLogN.KFW.topC jT jL) (hW : tbl jW = lowC jW jL) (hL : tbl jL = levC jL rowC)
    {K r Z Zr P D S ρ p w k q0 Bp H Mb Bz : ℕ} {Kc : ℝ}
    (hk : k = Nat.log mC D) (hq : q0 = q0f D k)
    (hBp : Bp = padB (P * 2 ^ (K * q0)) (P8Lift.Wc ^ k)) (hH : H = w + KFM.EwB NLogN.KFW.A0 D)
    (LV : ∀ j, LvQ Isym tbl jL rowC K r Z Zr H j (cbW Kc K j))
    (hρ : ρ < K) (hK : 1 ≤ K) (hS : 1 ≤ S) (hP : 1 ≤ P) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (hZ32 : zsz ((32 * (P * 2 ^ (K * D) * S * r) : ℕ) : ℤ) ≤ Z)
    (hVt : zsz ((Vb K (K * D) S r H 0 P : ℕ) : ℤ) ≤ Zr)
    (hVl : ∀ j ≤ k, zsz ((Vb K (K * (D - q0)) S r H j Bp : ℕ) : ℤ) ≤ Zr)
    (hMb : zsz (Mb : ℤ) ≤ Bz) (hM : MbB K P D w k q0 Bp ≤ Mb)
    (hEZ : zsz (((q0 + lowF ES k (D - q0) + (D / 2 + D % 2)) : ℕ) : ℤ) ≤ Z)
    (hp : zsz (p : ℤ) ≤ Z) (hwZ : w < 2 ^ Z)
    (st : IState HS) (f : Fin HS → List ℤ) (zs : List GI) (l : List ℤ)
    (xs : List (Fin r → ℂ)) (hx : RecRep r p zs xs)
    (hl : xs.length = AModel.vol (Butterfly.layerShape P K D S)) (h0 : f 0 = gflat zs ++ l)
    (h36 : f 36 = [(P : ℤ), (K : ℤ), (D : ℤ), (S : ℤ), (ρ : ℤ), (r : ℤ), (p : ℤ), (w : ℤ), (Z : ℤ)])
    (hfree : ∀ j : Fin HS, j ≠ 0 → j ≠ 36 → j.val < 50 → f j = [])
    (hb : NLogN.KFB.GB w zs) (hdisk : ∀ j (h : j < xs.length), ‖xs[j]‖ ≤ 1)
    (hex : ∃ zs', RecRep r p zs' (Butterfly.prop14Proc (P := P) (S := S) hρ p
        (Butterfly.tens Butterfly.Cm : Butterfly.Op (Fin D)) xs)) :
    IRuns Isym tbl (p14C jG) (NLogN.KIL.encK st f)
      (NLogN.KIL.encK st (Function.update f 0 (gflat (Classical.choose hex) ++ l)))
      (8 * (2 * moveCost Z + 19) + (cChain Kc K S r H P D k q0 Bp Z Zr Bz w +
        8 * (2 * moveCost Z + 19))) := by sorry
