-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_NLogN_KFM_prop14Ph_kTable
-- name    : IntMul.OpenAI.R129.P.NLogN.KFM.prop14Ph_kTable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:05.795767+00:00
-- url     : https://prove2.me/theorems/a4a92fcb-84c0-46f8-b2b7-ebb40da3df99
-- title:
--   Proposition 14 in IL, unconditional, in the merged table (λ = τ50) (κ = 2⁻¹²⁹ constants)
-- statement:
--   **Proposition 14 in IL, unconditional, in the merged table (λ = τ50)**, at the `same-network-129` constants.
--
--   This is `NLogN.KFM.prop14Ph_kTable` from xuanji's $\kappa = 2^{-182}$ formalization (statement and proof unchanged apart from the constants) with the constants of §8 replaced by those of the community patch `same-network-129`: $\tau = 1 - 2^{-42}$ (same swap networks, motif exponent from $\log 10^6 < 14$), $\varepsilon = c = 2^{-43}$, $\lambda' = 1 - 2^{-85}$ ($\delta = 1/16$ unchanged). The parameter map $d = \lfloor b^{\varepsilon} \rfloor$, $K = \lfloor d^{c} \rfloor$, $\ell = \lceil L/d \rceil$, $\alpha = \lceil (12 d^2 b)^{1/4} \rceil$, $r = 2^{\ell}$ is the one of `Def_IntMul_OpenAI_R129`, and every constant-dependent name lives under `IntMul.OpenAI.R129.P`.
--
--   **Context.** The lemma belongs to the part *KFM 7: one procedure table for Lemma 12 / Prop 14 and the FM multiplier*: Procedure tables are merged by renaming procedure indices (`IStmt.ren id g`, nlogn `HRen`).
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of `NLogN.KFM.prop14Ph_kTable` (https://prove2.me/theorems/712db8bb-aa1c-47d9-a3fc-60bfd10ffe67).

import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM
open Complex
open _root_.IntMul
open _root_.NLogN.RS
open _root_.AModel hiding hdPos
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFD
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.NLogN.KFG hiding cPair imE mulB reE tsE
open _root_.NLogN.KFH
open _root_.NLogN.KFN hiding cMv pcs τ50
open _root_.IntMul.OpenAI.R129.P.NLogN.KFN
open _root_.P8Lift
open _root_.Butterfly hiding Op
variable {E : ℕ}

open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R129.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL PhiNeed QRegs SwapNeed TrRegs TransNeed bLn baseSt bigP bsN cLineU cPhiU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV phiG prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R129.P.NLogN.KFM

theorem IntMul.OpenAI.R129.P.NLogN.KFM.prop14Ph_kTable (ext : Fin E → IStmt HS (7 + E)) : ∃ (A : ℕ) (Kc : ℝ), 0 < Kc ∧
    ∀ (Isym : List Sym) {K r Z : ℕ}, 6 ≤ K → 1 ≤ r → 80 * Z * (Z + 2) ≤ 2 ^ K →
    let CR : ℝ := Kc * (K + 2) + 1
    let Ψ : ℕ → ℕ := KFR.PsiR r Z
    ∀ {P D S ρ : ℕ} (hρ : ρ < K), 1 ≤ S → 1 ≤ P → 1 ≤ D →
    zsz ((32 * (vol (Butterfly.layerShape P K D S) * r) : ℕ) : ℤ) ≤ Z →
    ∃ (Cc : ℕ → IStmt HS (7 + E)) (E dC : ℕ) (kC : ℕ → ℕ),
      E ≤ D + (Nat.log (100 ^ 3) D + 1) * 100 ^ 3 * ((Nat.log (100 ^ 3) D + 1) *
        NLogN.KFN.Gb P8Lift.complexIface.net.length P8Lift.sc P8Lift.Wc A ^ Nat.log (100 ^ 3) D) ∧
      dC ≤ 2 * D + (Nat.log (100 ^ 3) D + 1) * 100 ^ 3 * (4 * (Nat.log (100 ^ 3) D + 1) ^ 2 *
        NLogN.KFN.Gb P8Lift.complexIface.net.length P8Lift.sc P8Lift.Wc A ^ (Nat.log (100 ^ 3) D + 2)) ∧
      (∀ w, (kC w : ℝ) ≤ (2 * ((((Nat.log (100 ^ 3) D + 1) * 100 ^ 3 : ℕ) : ℝ) *
          ((100000 + (Nat.log (100 ^ 3) D : ℝ) *
            (((P8Lift.sc + P8Lift.complexIface.net.length) * alN P8Lift.Wc A + 1 : ℕ) : ℝ) +
            (Nat.log (100 ^ 3) D : ℝ) *
              (2 * (((P8Lift.sc + P8Lift.complexIface.net.length : ℕ) : ℝ) * CR))) *
            (D : ℝ) ^ τ50) + 1) + 1000000 * (((Nat.log (100 ^ 3) D * 71 : ℕ) : ℝ) + 2)) *
        ((vol (Butterfly.layerShape P K D S) : ℕ) : ℝ) *
        (Xf r Ψ (w + 2 * D + (Nat.log (100 ^ 3) D + 1) * 100 ^ 3 *
          (4 * (Nat.log (100 ^ 3) D + 1) ^ 2 *
            NLogN.KFN.Gb P8Lift.complexIface.net.length P8Lift.sc P8Lift.Wc A ^ (Nat.log (100 ^ 3) D + 2)) +
          20 * (Nat.log (100 ^ 3) D + 1) ^ 3 *
            NLogN.KFN.Gb P8Lift.complexIface.net.length P8Lift.sc P8Lift.Wc A ^ (Nat.log (100 ^ 3) D + 2) +
          2) : ℝ)) ∧
      ∀ (st : IState HS) (f : Fin HS → List ℤ) (zs : List GI) (l : List ℤ)
        (xs : List (Fin r → ℂ)) (p w : ℕ), RecRep r p zs xs →
        xs.length = vol (Butterfly.layerShape P K D S) → f 0 = gflat zs ++ l → ClN f →
        NLogN.KFB.GB w zs → (∀ j (h : j < xs.length), ‖xs[j]‖ ≤ 1) →
        ∃ zs', RecRep r p zs' (Butterfly.prop14Proc (P := P) (S := S) hρ p
            (Butterfly.tens Butterfly.Cm : Butterfly.Op (Fin D)) xs) ∧
          NLogN.KFB.GB (p + 1) zs' ∧
          (∀ j (h : j < (Butterfly.prop14Proc (P := P) (S := S) hρ p
              (Butterfly.tens Butterfly.Cm : Butterfly.Op (Fin D)) xs).length)
            (h' : j < (Butterfly.layerH P K D S ρ hρ xs).length), ∀ c,
            ‖(Butterfly.prop14Proc (P := P) (S := S) hρ p
              (Butterfly.tens Butterfly.Cm : Butterfly.Op (Fin D)) xs)[j] c -
              (Butterfly.layerH P K D S ρ hρ xs)[j] c‖ < Real.sqrt 2 * 2⁻¹ ^ p) ∧
          IRuns Isym (kTable ext) (p14Ph P K D S ρ r E dC Cc w) (encK st f)
            (encK st (Function.update f 0 (gflat zs' ++ l)))
            (kC w + cWrapPh P K D S r E
              (zsz ((16 * (vol (Butterfly.layerShape P K D S) * r) : ℕ) : ℤ)) w dC) := by sorry
