-- Prove2me | Theorems.Thm_J6Seg_Ax_axA_pass
-- name    : J6Seg.Ax.axA_pass
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-20T20:59:02.361325+00:00
-- url     : https://prove2.me/theorems/a8cc7581-997c-4b06-aadb-32f088508143
-- title:
--   One `A` axis as a `PassOK` step (round six, `axA_pass`)
-- statement:
--   **One `A` axis as a `PassOK` step.**
--
--   The following holds (Lean statement, in the scope of module `Solutions.J6SegAxA5`):
--
--   ```lean
--   theorem J6Seg.Ax.axA_pass {Pp : ℕ} {Isym : List Sym} {tbl : Fin Pp → IStmt HS Pp}
--       {eF eB e pM eUp eDn : Fin Pp} {dA dF : Fin HS} {ρ : Fin 19 → Fin HS} {desc : List ℤ}
--       {C₀ Cs Cp C1 : ℝ}
--       {st1 u2 d2 u3 d3 u4 d4 u5 d5 u6 d6 u8 d8 : IStmt HS Pp}
--       {p s t α H pk b w f pre post : ℕ} {φ1 φ2 B BH Bk Lmax : ℕ} {Ka Kr Kc X0 : ℤ}
--       (hA0 : dA ≠ 0) (hF0 : dF ≠ 0) (hFA : dF ≠ dA) (hfree : SlabFree dA)
--       (hR : RegOK ρ KR.dT dF) (hρA : ∀ i, ρ i ≠ dA) (hTA : KR.dT ≠ dA)
--       (hFine : FineBody6 Isym tbl eF eB dF C₀)
--       (hMul : MulOK Isym tbl pM NLogN.KFUU.MS) (hE : tbl e = aKprog2 pM)
--       -- geometry
--       (hf : 2 ^ f = 8 * H) (hpre0 : 0 < pre) (ht0 : 0 < t) (hp : 0 < post) (hH : 1 ≤ H) (hM0 : 0 < t / (16 * H))
--       (hsG : MonoSrc (32 * t) (8 * (t / (16 * H) * (8 * H)))
--         (J6A.srcG s t H (J6A.WA p α H) (t / (16 * H)) (8 * H)))
--       (hsC : MonoSrc (t / (16 * H) * 8 * (8 * H)) t (J6A.srcC H (8 * H)))
--       (hK : AKCond p s t α H pk b w f pre post φ1 φ2 B BH Bk Lmax Ka Kr Kc X0)
--       -- the steps and set-ups
--       (h1 : PassOK Isym tbl st1 dA desc (fun L => L.length = pre * (t * post) ∧ GB w L)
--         (J6A.dupL 32) C1)
--       (hS2 : SetupS Isym tbl u2 d2 ![dF] dA desc ![descFine w 5 1 (pre * (t * post))] Cs)
--       (hS3 : SetupS Isym tbl u3 d3 ![dF] dA desc ![descFine w 5 pre (t * post)] Cs)
--       (hS4 : SetupS Isym tbl u4 d4 ρS dA desc
--         (slabV (ctlOf (32 * t) (8 * (t / (16 * H) * (8 * H)))
--           (J6A.srcG s t H (J6A.WA p α H) (t / (16 * H)) (8 * H)) (fun _ => 0)) pre post
--           (8 * (t / (16 * H) * (8 * H))) [] []) Cs)
--       (hS5 : SetupS Isym tbl u5 d5 ![dF] dA desc
--         ![descFine w 3 pre (t / (16 * H) * (8 * H) * post)] Cs)
--       (hS6 : SetupS Isym tbl u6 d6 ![dF] dA desc
--         ![descFine w 3 (pre * (t / (16 * H))) (8 * H * post)] Cs)
--       (hSK : SetupBody6 Isym tbl eUp eDn ρ dA desc
--         (kerRegs w (pk + 1) f pre (t / (16 * H) * 8) post
--           (tabsT (aTabG p s t α H pk b) (t / (16 * H) * 8))) Cp)
--       (hS8 : SetupS Isym tbl u8 d8 ρS dA desc
--         (slabV (ctlOf (t / (16 * H) * 8 * (8 * H)) t (J6A.srcC H (8 * H)) (fun _ => 0)) pre post t
--           [] []) Cs) :
--       PassOK Isym tbl
--         (axAProg st1 (fxSt u2 d2 eF) (fxSt u3 d3 eB)
--           (slSt u4 d4 (J6Seg.Slab.passP (.op (.drop 0)) (.op (.mv 0 Slab.rT)) itI (.op (.mv Slab.rT 0))))
--           (fxSt u5 d5 eF) (fxSt u6 d6 eB) (kpSt eUp eDn ρ KR.dT dF eF eB e)
--           (slSt u8 d8 (J6Seg.Slab.passP (.op (.drop 0)) (.op (.mv 0 Slab.rT)) itI (.op (.mv Slab.rT 0)))))
--         dA desc (fun L => L.length = pre * (t * post) ∧ GB w L) (J6A.pipeAL p s t α H pre post)
--         (axACost C₀ Cs Cp C1 p s t α H pk b w f pre post φ1 φ2 B BH Bk Lmax)
--   ```
--
--   **Context.** `A`-line axis program (`AxisUA6`), part 5: the eight steps of one axis
--
--   **`axA_pass`**: the program
--   `axAProg dup (fx f=5 fwd) (fx f=5 back) (gather slab) (fx f=3 fwd) (fx f=3 back) (kernel) (compress slab)`
--   is a `PassOK` step for `J6A.pipeAL p s t α H pre post` on arrays of length `pre · t · post` with
--   `GB w`, from:
--
--   * the fine exposure `FineBody6` on `dF` and four `SetupS` pairs putting `descFine …` on `dF`;
--   * two slab `SetupS` pairs (`ρS`) for the gather (`srcG`) and compress (`srcC`) slab passes;
--   * the copy step (`dupL 32`) as a `PassOK` step;
--   * the `A` kernel (`tbl e = aKprog2 pM`, `J6AIL4b`) with its register set-up `SetupBody6` (`kerRegs`,
--     as `PreA6` provides it) and the numeric side conditions **`AKCond`** (those of `aK_row` and of
--     `kpass_ok`, `J6SegAxis2`).
--
--   The cost is **`axACost`**.
--
--   **Formalization Note.** Part of the Lean formalization of the round-six κ-improvement (integer-multiplication-kappa campaign, target `IntMul.Kappa.jain_round6_framework`). The statement is copied verbatim from the Lean development; the platform node carries the same declaration name. Definitions it mentions live in the `IntMul_Kappa_R6_Defs*` bundles (on top of the published κ bundles `IntMul_Kappa_K_Defs*`).
-- source:
--   S. Jain, round-six networks for the integer-multiplication κ-improvement campaign (https://github.com/Swapnil-jain/integer-mult-kappa, commit 5868dc7) and D. Colkitt, integer-mult-bounds (https://github.com/CrocSwap/integer-mult-bounds); target `IntMul.Kappa.jain_round6_framework`. Lean declaration `J6Seg.Ax.axA_pass`, Solutions/J6SegAxA5.lean (lines 110–178) of the round-six development.

-- Round-six κ development (integer-multiplication-kappa), generated by skeleton subtraction.

import Definitions.Def_IntMul_Kappa_R6_Defs68

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open J6Seg J6Seg.Ax
open IntMul NLogN NLogN.KIL NLogN.KFB IntMul.Kappa.R6 Function J6Seg.KR.AK
open J6Seg.Slab
open NLogN.KFUU (lA lC lD)

theorem J6Seg.Ax.axA_pass {Pp : ℕ} {Isym : List Sym} {tbl : Fin Pp → IStmt HS Pp}
    {eF eB e pM eUp eDn : Fin Pp} {dA dF : Fin HS} {ρ : Fin 19 → Fin HS} {desc : List ℤ}
    {C₀ Cs Cp C1 : ℝ}
    {st1 u2 d2 u3 d3 u4 d4 u5 d5 u6 d6 u8 d8 : IStmt HS Pp}
    {p s t α H pk b w f pre post : ℕ} {φ1 φ2 B BH Bk Lmax : ℕ} {Ka Kr Kc X0 : ℤ}
    (hA0 : dA ≠ 0) (hF0 : dF ≠ 0) (hFA : dF ≠ dA) (hfree : SlabFree dA)
    (hR : RegOK ρ KR.dT dF) (hρA : ∀ i, ρ i ≠ dA) (hTA : KR.dT ≠ dA)
    (hFine : FineBody6 Isym tbl eF eB dF C₀)
    (hMul : MulOK Isym tbl pM NLogN.KFUU.MS) (hE : tbl e = aKprog2 pM)
    -- geometry
    (hf : 2 ^ f = 8 * H) (hpre0 : 0 < pre) (ht0 : 0 < t) (hp : 0 < post) (hH : 1 ≤ H) (hM0 : 0 < t / (16 * H))
    (hsG : MonoSrc (32 * t) (8 * (t / (16 * H) * (8 * H)))
      (J6A.srcG s t H (J6A.WA p α H) (t / (16 * H)) (8 * H)))
    (hsC : MonoSrc (t / (16 * H) * 8 * (8 * H)) t (J6A.srcC H (8 * H)))
    (hK : AKCond p s t α H pk b w f pre post φ1 φ2 B BH Bk Lmax Ka Kr Kc X0)
    -- the steps and set-ups
    (h1 : PassOK Isym tbl st1 dA desc (fun L => L.length = pre * (t * post) ∧ GB w L)
      (J6A.dupL 32) C1)
    (hS2 : SetupS Isym tbl u2 d2 ![dF] dA desc ![descFine w 5 1 (pre * (t * post))] Cs)
    (hS3 : SetupS Isym tbl u3 d3 ![dF] dA desc ![descFine w 5 pre (t * post)] Cs)
    (hS4 : SetupS Isym tbl u4 d4 ρS dA desc
      (slabV (ctlOf (32 * t) (8 * (t / (16 * H) * (8 * H)))
        (J6A.srcG s t H (J6A.WA p α H) (t / (16 * H)) (8 * H)) (fun _ => 0)) pre post
        (8 * (t / (16 * H) * (8 * H))) [] []) Cs)
    (hS5 : SetupS Isym tbl u5 d5 ![dF] dA desc
      ![descFine w 3 pre (t / (16 * H) * (8 * H) * post)] Cs)
    (hS6 : SetupS Isym tbl u6 d6 ![dF] dA desc
      ![descFine w 3 (pre * (t / (16 * H))) (8 * H * post)] Cs)
    (hSK : SetupBody6 Isym tbl eUp eDn ρ dA desc
      (kerRegs w (pk + 1) f pre (t / (16 * H) * 8) post
        (tabsT (aTabG p s t α H pk b) (t / (16 * H) * 8))) Cp)
    (hS8 : SetupS Isym tbl u8 d8 ρS dA desc
      (slabV (ctlOf (t / (16 * H) * 8 * (8 * H)) t (J6A.srcC H (8 * H)) (fun _ => 0)) pre post t
        [] []) Cs) :
    PassOK Isym tbl
      (axAProg st1 (fxSt u2 d2 eF) (fxSt u3 d3 eB)
        (slSt u4 d4 (J6Seg.Slab.passP (.op (.drop 0)) (.op (.mv 0 Slab.rT)) itI (.op (.mv Slab.rT 0))))
        (fxSt u5 d5 eF) (fxSt u6 d6 eB) (kpSt eUp eDn ρ KR.dT dF eF eB e)
        (slSt u8 d8 (J6Seg.Slab.passP (.op (.drop 0)) (.op (.mv 0 Slab.rT)) itI (.op (.mv Slab.rT 0)))))
      dA desc (fun L => L.length = pre * (t * post) ∧ GB w L) (J6A.pipeAL p s t α H pre post)
      (axACost C₀ Cs Cp C1 p s t α H pk b w f pre post φ1 φ2 B BH Bk Lmax) := by sorry
