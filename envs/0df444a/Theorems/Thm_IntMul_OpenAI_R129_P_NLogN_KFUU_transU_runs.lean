-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFUU_transU_runs
-- name    : IntMul.OpenAI.R129.P.NLogN.KFUU.transU_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:24.119662+00:00
-- url     : https://prove2.me/theorems/5510ffa3-8e06-4313-9efe-c6c03b069ade
-- title:
--   transU_runs (KFUU §11b: the uniform axis rotation `transU`) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **transU_runs (KFUU §11b: the uniform axis rotation `transU`)**, at the `same-network-129` constants.
--
--   This is `NLogN.KFUU.transU_runs` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFUU §11b: the uniform axis rotation `transU`*: `readT` reads `descTr w h bs = [w, h, k, b_0, …]` from `dP` (restored); `mkT` builds `2^h`,
--   the sizes `t_j = 2^{h+b_j}` (on `pTK` and `xB`), `nR = k`, `rCZ = 2`; the first `revU`
--   reverses all `k` axes; `midT` sets `rCZ = 2 t_0`, the sizes `t_{k-1}, …, t_1` on `pTR`,
--   `nR = k - 1`; the second `revU` reverses the first `k - 1` axes (inner block `2 t_0`);
--   `cleanT` clears. **`transU_runs`**: the result is `gflat (transposeL t_0 (V / t_0) zs)`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFUU.transU_runs` (https://prove2.me/theorems/b8e9f0e9-8c1a-4262-9759-b14ff18e259b).

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
set_option maxHeartbeats 64000000

open _root_.NLogN hiding cE mvK tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFUU hiding SwOKU cBwd cFwd cRevU cSwN cSwV cTr
open _root_.IntMul.OpenAI.R129.P.NLogN.KFUU

theorem IntMul.OpenAI.R129.P.NLogN.KFUU.transU_runs {pM : Fin P} (hM : MulOK I iprog pM NLogN.KFUU.MS) {eSw : Fin P} {sdS : Fin HS} {K : ℝ}
    (hK : SwOKU I iprog eSw sdS K) (hdS : sdS ≠ 0) {Dsc : Fin HS} (hD : Dsc = 18 ∨ Dsc = 19)
    (hDd : Dsc ≠ sdS) (w h : ℕ) (b0 : Bool) (bt : List Bool) (hh : 1 ≤ h)
    (s : IState HS) (f : Fin HS → List ℤ) (l : List ℤ) (hf : ∀ j, j ≠ 0 → j ≠ _root_.NLogN.KFUU.dP → f j = [])
    (hfd : f _root_.NLogN.KFUU.dP = KFM.descTr w h (b0 :: bt)) (zs : List GI) (h0 : f 0 = gflat zs ++ l)
    (hlen : zs.length = vol (shP h (b0 :: bt))) (hgb : NLogN.KFB.GB w zs)
    (B Z : ℕ) (hwB : zsz (w : ℤ) ≤ B) (hhB : h + 1 ≤ B)
    (h2B : zsz ((2 * 2 ^ (h + if b0 then 1 else 0) : ℕ) : ℤ) ≤ B)
    (h2hB : zsz ((2 ^ h * 2 : ℕ) : ℤ) ≤ B)
    (hkB : zsz ((3 + (b0 :: bt).length : ℕ) : ℤ) ≤ B)
    (hZ3 : 3 ≤ Z) (hZV : zsz ((vol (shP h (b0 :: bt)) * 2 : ℕ) : ℤ) ≤ Z) (hwZ : zsz (w : ℤ) ≤ Z)
    (hUZ : zsz ((2 ^ h : ℕ) : ℤ) ≤ Z) :
    IRuns I iprog (transU pM eSw sdS Dsc) (NLogN.KIL.encK s f)
      (NLogN.KIL.encK s (Function.update f 0 (gflat (IntMul.HvdH.Ref.transposeL
        ((shP h (b0 :: bt)).headD 1) (vol (shP h (b0 :: bt)).tail) zs) ++ l)))
      (cTr K w h (b0 :: bt) B Z) := by sorry
