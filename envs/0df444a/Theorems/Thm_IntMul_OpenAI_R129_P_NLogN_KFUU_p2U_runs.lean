-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFUU_p2U_runs
-- name    : IntMul.OpenAI.R129.P.NLogN.KFUU.p2U_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:18.196921+00:00
-- url     : https://prove2.me/theorems/8dde2c1b-c622-4a03-9e0b-5819eed523cd
-- title:
--   p2U_runs (KFUU §2i: phase 2 in IL) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **p2U_runs (KFUU §2i: phase 2 in IL)**, at the `same-network-129` constants.
--
--   This is `NLogN.KFUU.p2U_runs` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFUU §2i: phase 2 in IL*: `p2U` computes `vol ctB · cr` (from `vol (shP u bs)`, `U^n` and `cz = 2 cr`) and `⌊n/2⌋`, then
--   runs the `⌊n/2⌋` swaps. The main fields are reversed: the layout `lay1 bg n 0` becomes
--   `rv n (n/2) (lay1 bg n 0)`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFUU.p2U_runs` (https://prove2.me/theorems/8966cb42-29af-4205-8547-2f496f47b2d8).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 20000
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
set_option maxHeartbeats 8000000

open _root_.NLogN hiding cE mvK tE
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFUU hiding SwOKU cBwd cFwd cRevU cSwN cSwV cTr
open _root_.IntMul.OpenAI.R129.P.NLogN.KFUU

theorem IntMul.OpenAI.R129.P.NLogN.KFUU.p2U_runs {pM : Fin P} (hMul : MulOK I iprog pM NLogN.KFUU.MS) {pS : Fin HS} (hpS : LS pS)
    {eSw : Fin P} {dS : Fin HS} {K : ℝ} (hK : SwOKU I iprog eSw dS K) (hdS : dS ≠ 0)
    {Dsc : Fin HS} (hD : Dsc = 18 ∨ Dsc = 19) (hDd : Dsc ≠ dS)
    (u w cz cr : ℕ) (bs : List Bool) (hu : 1 ≤ u) (hcz : cz = 2 * cr) (hcr : 1 ≤ cr)
    (xs0 : List ℤ) (hx : Bnd w xs0) (Z : ℕ) (hZ3 : 3 ≤ Z)
    (hVZ : zsz ((vol (shP u bs) * cz : ℕ) : ℤ) ≤ Z) (zw : zsz (w : ℤ) ≤ Z)
    (zU : zsz ((2 ^ u : ℕ) : ℤ) ≤ Z)
    (t : IState HS) (R : List Item)
    (h0 : t.G 0 = ints (Dl (mzB u bs.length cz) (bgB bs) (List.range bs.length ++ [bs.length])
      (lay1 (bgB bs) bs.length 0) xs0 0) ++ R)
    {RS LN LZ LW LU L2 : List Item}
    (hpS0 : t.G pS = ints (NLogN.KFUU.zl (shP u bs)) ++ RS) (hN : t.G nR = .int (bs.length : ℤ) :: LN)
    (hZ : t.G rCZ = .int (cz : ℤ) :: LZ)
    (hW : t.G rW = .int (w : ℤ) :: LW) (hUu : t.G NLogN.KFUU.rU = .int (u : ℤ) :: LU)
    (h2 : t.G rU2 = .int ((2 ^ u : ℕ) : ℤ) :: L2) :
    IRuns I iprog (p2U pM pS eSw dS Dsc) t
      (t.upd 0 (ints (Dl (mzB u bs.length cz) (bgB bs) (List.range bs.length ++ [bs.length])
        (((lay1 (bgB bs) bs.length 0).take bs.length).reverse ++
          (lay1 (bgB bs) bs.length 0).drop bs.length) xs0 0) ++ R))
      ((bs.length + 1) * (⌈cSwV K w u (vol (shP u bs) * cr)⌉₊ + 40 * cU Z) + 30 * cU Z) := by sorry
