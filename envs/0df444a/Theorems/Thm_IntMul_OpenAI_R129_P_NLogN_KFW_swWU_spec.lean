-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFW_swWU_spec
-- name    : IntMul.OpenAI.R129.P.NLogN.KFW.swWU_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:30.581377+00:00
-- url     : https://prove2.me/theorems/5c7f82ea-6481-4446-9067-d725159f37b0
-- title:
--   Uniform Lemma 12 on w-bit integer arrays (KFS.swW_spec with the registers sW = w, sU = u, sN = V, sP = vol… (κ = 2⁻¹²⁹ constants)
-- statement:
--   **Uniform Lemma 12 on w-bit integer arrays (KFS.swW_spec with the registers sW = w, sU = u, sN = V, sP = vol…**, at the `same-network-129` constants.
--
--   This is `NLogN.KFW.swWU_spec` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFW: uniform Lemma 12 on integer arrays (parameters in registers)*.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFW.swWU_spec` (https://prove2.me/theorems/668811bd-f7b1-45ed-bcc0-245dce6d9cd7).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open _root_.NLogN hiding padL vE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFW hiding RowU RowUP cBody cCL cChain cLowP cLowPart cTot cbW clF coefF
open _root_.IntMul.OpenAI.R129.P.NLogN.KFW
open _root_.IntMul
open _root_.NLogN.RS
open _root_.NLogN.KFW.RS
open _root_.NLogN.KIL hiding Cfg FR FrOK St aE bodyU cBody fIn kS negP outR pT padL rowR stD
open _root_.NLogN.KFD hiding levF scr
open _root_.NLogN.KFE
open _root_.NLogN.KFB hiding permL permP
open _root_.NLogN.KFL hiding LinesOK P1 SwOK cT coreCost sT uE
open _root_.IntMul.OpenAI.R129.P.NLogN.KFL
open _root_.NLogN.KFS hiding τS
open _root_.IntMul.OpenAI.R129.P.NLogN.KFS
open _root_.NLogN.KFV hiding Cost18 EwB18 Log18Need P14Need P14Uat Par18Need SwOK cBody3 cBody3R cChunk cLayIn cLayOut cPh3 cPh3R cXch gT posE sT tE topC total18 truncU twA twB vB vE vT vX zX
open _root_.IntMul.OpenAI.R129.P.NLogN.KFV
open _root_.AModel hiding hdPos logStep stepC
open _root_.AModelL12
open _root_.NetProp7
variable {Pp : ℕ} {I : List Sym} {iprog : Fin Pp → IStmt HS Pp}

open _root_.NLogN hiding padL vE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFW hiding RowU RowUP cBody cCL cChain cLowP cLowPart cTot cbW clF coefF
open _root_.IntMul.OpenAI.R129.P.NLogN.KFW

theorem IntMul.OpenAI.R129.P.NLogN.KFW.swWU_spec :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (u w : ℕ) (Pre G Suf : Shape), 1 ≤ u →
      (∀ a ∈ Pre, 1 ≤ a) → (∀ a ∈ G, 1 ≤ a) → (∀ a ∈ Suf, 1 ≤ a) →
      ∀ (I : List Sym) (t : IState HS) (xs : List ℤ) (R : List Item),
      t.G 0 = ints xs ++ R → xs.length = vol (binShape Pre G Suf (2 ^ u)) →
      (∀ x ∈ xs, zsz x ≤ w) →
      ∀ {L1 L2 L3 L4 L5 L6 : List Item},
      t.G sN = .int (vol (binShape Pre G Suf (2 ^ u)) : ℤ) :: L1 → t.G NLogN.KFW.sW = .int (w : ℤ) :: L2 →
      t.G NLogN.KFW.sP = .int (vol Pre : ℤ) :: L3 → t.G sG = .int (vol G : ℤ) :: L4 →
      t.G sS = .int ((vol Suf * (w + 1) : ℕ) : ℤ) :: L5 → t.G sU = .int (u : ℤ) :: L6 →
      ∃ c : ℕ, IRuns I l12prog (swWU q) t
        (t.upd 0 (ints (pull (binShape Pre G Suf (2 ^ u)) (binShape Pre G Suf (2 ^ u))
          (swapPos Pre.length (Pre.length + 1 + G.length)) 0 xs) ++ R)) c ∧
        (c : ℝ) ≤ K * ((w : ℝ) + 1) * ((vol (binShape Pre G Suf (2 ^ u)) : ℝ) + 1) *
          (u : ℝ) ^ τS := by sorry
