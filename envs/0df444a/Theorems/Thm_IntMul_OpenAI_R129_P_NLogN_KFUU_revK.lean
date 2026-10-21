-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFUU_revK
-- name    : IntMul.OpenAI.R129.P.NLogN.KFUU.revK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:26:54.056982+00:00
-- url     : https://prove2.me/theorems/a40fd018-e29d-4327-aa64-d0a85b393644
-- title:
--   revK (KFUU §9a: the passes on managed states) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **revK (KFUU §9a: the passes on managed states)**, at the `same-network-129` constants.
--
--   This is `NLogN.KFUU.revK` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFUU §9a: the passes on managed states*: The pass lemmas (`padAllU_runs`, `unpadAllU_runs`, `revU_runs`, `rotsFU_runs`, `rotsBU_runs`)
--   restated on managed states `encK s F` (data `xs ++ l` on stack `0`).
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFUU.revK` (https://prove2.me/theorems/8557167d-b40c-477c-a1ac-49f4c4042c71).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
open _root_.NLogN hiding cE mvK tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFUU hiding SwOKU cBwd cFwd cRevU cSwN cSwV cTr
open _root_.IntMul.OpenAI.R129.P.NLogN.KFUU
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR PushOK St aE cBwd cFwd dP dropK negP outR padL postB preB shP sufV tB xA
open _root_.NLogN.KFB hiding mvL permL permP rB
open _root_.NLogN.KFC hiding enc encF isPos rW
open _root_.NLogN.KFT hiding tE tT
open _root_.NLogN.KFU hiding SwOK cPhi oD
open _root_.IntMul.OpenAI.R129.P.NLogN.KFU
open _root_.AModel hiding hdPos
open _root_.AModelL12
variable {P : ℕ} {I : List Sym} {iprog : Fin P → IStmt HS P}

open _root_.NLogN hiding cE mvK tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFUU hiding SwOKU cBwd cFwd cRevU cSwN cSwV cTr
open _root_.IntMul.OpenAI.R129.P.NLogN.KFUU

theorem IntMul.OpenAI.R129.P.NLogN.KFUU.revK {pM : Fin P} (hM : MulOK I iprog pM NLogN.KFUU.MS) {pS : Fin HS} (hpS : LS pS)
    {eSw : Fin P} {dS : Fin HS} {K : ℝ} (hK : SwOKU I iprog eSw dS K) (hdS : dS ≠ 0)
    {Dsc : Fin HS} (hD : Dsc = 18 ∨ Dsc = 19) (hDd : Dsc ≠ dS)
    (u w cz cr : ℕ) (bs : List Bool) (hu : 1 ≤ u) (hcz : cz = 2 * cr) (hcr : 1 ≤ cr)
    (xs0 : List ℤ) (hxs : xs0.length = vol (shP u bs) * cz) (hx : Bnd w xs0) (Z : ℕ) (hZ3 : 3 ≤ Z)
    (hVZ : zsz ((vol (shP u bs) * cz : ℕ) : ℤ) ≤ Z) (zw : zsz (w : ℤ) ≤ Z)
    (zU : zsz ((2 ^ u : ℕ) : ℤ) ≤ Z)
    (s : IState HS) (F : Fin HS → List ℤ) (l rS rN rZ rW' rU' r2 : List ℤ) (h0 : F 0 = xs0 ++ l)
    (hpS0 : F pS = NLogN.KFUU.zl (shP u bs) ++ rS) (hN : F nR = (bs.length : ℤ) :: rN)
    (hZ : F rCZ = (cz : ℤ) :: rZ) (hW : F rW = (w : ℤ) :: rW') (hUu : F NLogN.KFUU.rU = (u : ℤ) :: rU')
    (h2 : F rU2 = ((2 ^ u : ℕ) : ℤ) :: r2) :
    IRuns I iprog (revU pM pS eSw dS Dsc) (NLogN.KIL.encK s F)
      (NLogN.KIL.encK s (Function.update F 0
        (pull (shP u bs ++ [cz]) ((shP u bs).reverse ++ [cz]) (revH bs.length) 0 xs0 ++ l)))
      (cRevU K u w cz cr bs.length Z (vol (shP u bs))) := by sorry
