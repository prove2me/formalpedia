-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFV_fwd18_ok
-- name    : IntMul.OpenAI.R129.P.NLogN.KFV.fwd18_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:02.432964+00:00
-- url     : https://prove2.me/theorems/0beb3788-4ae5-40cd-aec8-f180d496ebcd
-- title:
--   fwd18_ok (KFV §51: the two layer programs of the Proposition 18 core) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **fwd18_ok (KFV §51: the two layer programs of the Proposition 18 core)**, at the `same-network-129` constants.
--
--   This is `NLogN.KFV.fwd18_ok` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFV §51: the two layer programs of the Proposition 18 core*: Both on the context `Ctx18` (layout registers and a round frame), with the chunk rounds given by
--   `ChunkU` (from the uniform Proposition 14) and the exchanges by `SwOK` (descriptor on stack `7`).
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFV.fwd18_ok` (https://prove2.me/theorems/16fedb26-bde8-47f4-99ff-3a9d44bdf513).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open _root_.NLogN hiding posE tE twA twB vE zX
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFV hiding Cost18 EwB18 Log18Need P14Need P14Uat Par18Need SwOK cBody3 cBody3R cChunk cLayIn cLayOut cPh3 cPh3R cXch total18
open _root_.IntMul.OpenAI.R129.P.NLogN.KFV
open _root_.IntMul
open _root_.NLogN.RS
open _root_.NLogN.KIL hiding Cfg FR St aE cBr cFwd cStep kG negP outR padL pre2 srcT swF yB
open _root_.NLogN.KFD
open _root_.NLogN.KFB hiding blk permL permP
open _root_.NLogN.KFH hiding gD
open _root_.NLogN.KFC hiding dbl enc encF mvB sT
open _root_.NLogN.KFT hiding tE
open _root_.Synth
open _root_.AModel hiding blk hdPos
open _root_.AModelL12
variable {Pp : ℕ} {I : List Sym} {iprog : Fin Pp → IStmt HS Pp}
open _root_.GlueLayout
open _root_.GlueP14 hiding blk cRec
open _root_.GlueError
variable (D ℓ K : ℕ) [NeZero D] (long : Fin D → Bool)
set_option maxHeartbeats 1000000

open _root_.NLogN hiding posE tE twA twB vE zX
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFV hiding Cost18 EwB18 Log18Need P14Need P14Uat Par18Need SwOK cBody3 cBody3R cChunk cLayIn cLayOut cPh3 cPh3R cXch total18
open _root_.IntMul.OpenAI.R129.P.NLogN.KFV

theorem IntMul.OpenAI.R129.P.NLogN.KFV.fwd18_ok (hK : 0 < K) (hℓ : 2 ≤ ℓ) (hq1 : 1 ≤ qq ℓ K) {e14 eSw : Fin Pp} {Kc : ℝ}
    (HSw : SwOK I iprog eSw dW18 Kc) (hKc : 0 ≤ Kc) {p W Z B cCh U : ℕ}
    (HC : ChunkU D ℓ K long I iprog e14 hK (by omega) p W Z cCh) (hW : p + 1 ≤ W)
    (hB : (pLP D ℓ K long).n + ℓ + 5 ≤ B) (hNB : D * qq ℓ K + D + 1 ≤ B) (hWB : W ≤ B)
    (hbL : bL D ℓ K long ≤ B) (hU : TwB D ℓ K long U) :
    LayerU (r := 2 ^ ℓ) I iprog (Ctx18 D ℓ K long p W Z) (fwd18 e14 eSw)
      (procQc p (paperLayout D ℓ K long hK (by omega)) ℓ (partAxes (al D ℓ long))
          (paperSel D ℓ K long hK (by omega)) ℓ ∘
        pull (binSh (pLP D ℓ K long).n) (binSh (pLP D ℓ K long).n)
          (relabel (initL D ℓ long) (tgtL D ℓ K long)) 0)
      (2 ^ (pLP D ℓ K long).n) p W
      (cLayIn D ℓ K long Kc (pLP D ℓ K long).n W B + NLogN.KFV.cFwd D ℓ K long W B cCh U) := by sorry
