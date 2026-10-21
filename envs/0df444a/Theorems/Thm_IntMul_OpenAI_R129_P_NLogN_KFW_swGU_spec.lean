-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFW_swGU_spec
-- name    : IntMul.OpenAI.R129.P.NLogN.KFW.swGU_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:33.42103+00:00
-- url     : https://prove2.me/theorems/c038458e-330c-4385-bf52-21c7c3a0a2fb
-- title:
--   Uniform Lemma 12 on Gaussian arrays in the l12prog table: KFS.swAxG_spec with w, u, p, q, sh read from the… (κ = 2⁻¹²⁹ constants)
-- statement:
--   **Uniform Lemma 12 on Gaussian arrays in the l12prog table: KFS.swAxG_spec with w, u, p, q, sh read from the…**, at the `same-network-129` constants.
--
--   This is `NLogN.KFW.swGU_spec` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFW: uniform Lemma 12 on Gaussian arrays (`SwapNeed`)*: `swGU q = descP ; swWU q ; popP`: read the descriptor `descSw w u p q sh` on `dS` into the
--   registers of `swWU` (`descP`), run the register-driven integer swap on the shape `sh ++ [2]`,
--   and pop the registers again.  **`swGU_spec`**, and **`swapNeed : KFM.SwapNeed`** with the table
--   `kTable (fun _ => (swGU q).ren id (gL 1))` (one fixed prime `q`).
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFW.swGU_spec` (https://prove2.me/theorems/231d24fd-a810-429f-b453-6edce774573f).

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
open _root_.NLogN.KFB hiding permL permP
open _root_.NLogN.KFS hiding τS
open _root_.IntMul.OpenAI.R129.P.NLogN.KFS
open _root_.NLogN.KFL hiding LinesOK P1 SwOK cT coreCost sT uE
open _root_.IntMul.OpenAI.R129.P.NLogN.KFL
open _root_.AModel hiding hdPos logStep stepC
open _root_.AModelL12

open _root_.NLogN hiding padL vE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFW hiding RowU RowUP cBody cCL cChain cLowP cLowPart cTot cbW clF coefF
open _root_.IntMul.OpenAI.R129.P.NLogN.KFW

theorem IntMul.OpenAI.R129.P.NLogN.KFW.swGU_spec :
    ∃ q₀ : ℕ, ∀ q', q'.Prime → q₀ < q' → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (u w : ℕ) (sh : Shape) (p q : ℕ), 1 ≤ u → (∀ a ∈ sh, 1 ≤ a) → p < q → q < sh.length →
      sh.getD p 0 = 2 ^ u → sh.getD q 0 = 2 ^ u →
      ∀ (I : List Sym) (s : IState HS) (f : Fin HS → List ℤ) (zs : List GI) (l : List ℤ),
      (∀ j, j ≠ 0 → j ≠ NLogN.KFW.dS → f j = []) → f NLogN.KFW.dS = KFM.descSw w u p q sh →
      f 0 = gflat zs ++ l → zs.length = vol sh → NLogN.KFB.GB w zs →
      ∃ c : ℕ, IRuns I l12prog (swGU q') (encK s f)
        (encK s (Function.update f 0 (gflat (pull sh sh (swapPos p q) 0 zs) ++ l))) c ∧
        (c : ℝ) ≤ K * (((w : ℝ) + 1) * ((vol sh : ℝ) + 1) * (u : ℝ) ^ τS +
          (((sh.length + 1) * (Nat.size (vol sh) + w + u + 1) ^ 2 : ℕ) : ℝ)) := by sorry
