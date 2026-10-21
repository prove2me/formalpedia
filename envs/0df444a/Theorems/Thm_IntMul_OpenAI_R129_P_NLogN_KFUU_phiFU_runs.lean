-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFUU_phiFU_runs
-- name    : IntMul.OpenAI.R129.P.NLogN.KFUU.phiFU_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:26.519222+00:00
-- url     : https://prove2.me/theorems/2d34d57a-a340-4f82-81de-c096c17f6740
-- title:
--   phiFU_runs (KFUU §9b: the uniform `Φ`) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **phiFU_runs (KFUU §9b: the uniform `Φ`)**, at the `same-network-129` constants.
--
--   This is `NLogN.KFUU.phiFU_runs` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFUU §9b: the uniform `Φ`*: `phiFU`: read the descriptor (`readD`), build the shape lists (`mkL`), pad `S_k → T_k`, reverse
--   (`revU`, the `SwapNeed` entry), unpad `T_r → S_r`, the `d` forward shifts (`rotsFU`), pad
--   `S_r → T_r`, clear. **`phiFU_runs`**: on the managed state of a `PhiNeed` call it computes
--   `KFU.PhiD`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFUU.phiFU_runs` (https://prove2.me/theorems/5c9e3060-3ba6-47cb-a864-a4b358cb2c34).

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

theorem IntMul.OpenAI.R129.P.NLogN.KFUU.phiFU_runs {pM : Fin P} (hM : MulOK I iprog pM NLogN.KFUU.MS) {eSw : Fin P} {sdS : Fin HS} {K : ℝ}
    (hK : SwOKU I iprog eSw sdS K) (hdS : sdS ≠ 0) {Dsc : Fin HS} (hD : Dsc = 18 ∨ Dsc = 19)
    (hDd : Dsc ≠ sdS) (w h d : ℕ) (bL : ℕ → Bool) (sF μ : ℕ → ℕ) (hh : 1 ≤ h)
    (hs : ∀ j < d, 1 ≤ sF j) (hst : ∀ j < d, sF j ≤ 2 ^ (h + if bL j then 1 else 0))
    (hμ : ∀ j < d, μ j < sF j)
    (s : IState HS) (f : Fin HS → List ℤ) (l : List ℤ) (hf : ∀ j, j ≠ 0 → j ≠ _root_.NLogN.KFUU.dP → f j = [])
    (hfd : f _root_.NLogN.KFUU.dP = KFM.descPhi w h d bL sF μ) (xs : List ℤ) (h0 : f 0 = xs ++ l)
    (hlen : xs.length = vol (shK d (NLogN.KFU.sP d sF))) (hb : Bnd w xs)
    (B Z Br Bb : ℕ) (hwB : zsz (w : ℤ) ≤ B) (hhB : h + 1 ≤ B) (h2B : zsz ((2 ^ h * 2 : ℕ) : ℤ) ≤ B)
    (h3B : zsz ((3 + 3 * d : ℕ) : ℤ) ≤ B) (hVB : zsz ((vol (NLogN.KFU.shR d (NLogN.KFU.sP d sF)) : ℕ) : ℤ) ≤ B)
    (hZ3 : 3 ≤ Z) (hZT : zsz ((vol (NLogN.KFU.shR d (NLogN.KFU.tP d h bL)) : ℕ) : ℤ) ≤ Z) (hwZ : zsz (w : ℤ) ≤ Z)
    (hUZ : zsz ((2 ^ h : ℕ) : ℤ) ≤ Z)
    (hVr : zsz ((vol (NLogN.KFU.shR d (NLogN.KFU.sP d sF)) : ℕ) : ℤ) ≤ Br) (hdr : zsz (d : ℤ) ≤ Br)
    (hVb : zsz ((vol (NLogN.KFU.shR d (NLogN.KFU.sP d sF)) : ℕ) : ℤ) ≤ Bb) :
    IRuns I iprog (phiFU pM eSw sdS Dsc) (NLogN.KIL.encK s f)
      (NLogN.KIL.encK s (Function.update f 0 (PhiD h d bL sF μ xs ++ l))) (IntMul.OpenAI.R129.P.NLogN.KFUU.cFwd K w h d bL sF B Z Br Bb) := by sorry
