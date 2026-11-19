-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeSeparatorOutput_exists_program_native
-- name    : Lax263307Proofs.NativeSeparatorOutput.exists_program_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:25.477847+00:00
-- url     : https://prove2.me/theorems/2b203bc0-a668-4666-903d-38305f543e86
-- title:
--   Fixed native separator-call output and component masks
-- statement:
--   Let $f$ be any polynomial word-RAM function. There is one fixed native program, fixed natural word/time/output polynomials and an encoding of its width polynomial. For every positive-order graph, positive load and bounded nonnegative rational load vector meeting the stated word and workspace guards, the native command preserves its complete context and writes the masks and records decoded from the same function $f$:
--
--   $$(\mathrm{remaining},\mathrm{separator},\mathrm{cuts},\mathrm{pieces})=\operatorname{decodeSeparatorOutput}(f).$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeSeparatorOutput.lean, theorem exists_program (lines 32–82)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax263307Proofs.NativeSeparatorOutput
end Lax263307Proofs.NativeSeparatorOutput

theorem Lax263307Proofs.NativeSeparatorOutput.exists_program_native : ∀ (f : List Nat → List Nat),
  Lax759944.RamPolytime.RamPolytime f →
    ∃ (p : Lax808846.Ram.Program) (wp : @Polynomial Nat Nat.instSemiring) (tp : @Polynomial Nat Nat.instSemiring) (op :
      @Polynomial Nat Nat.instSemiring) (coeff : List Nat),
      And
        (∀ (z : Nat),
          @Eq Nat (Lax455465Proofs.RamPolynomial.value coeff z) (@Polynomial.eval Nat Nat.instSemiring z wp))
        (∀ (b n load k h : Nat) (G : SimpleGraph (Fin n))
          [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (x : Fin n → NNRat),
          @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
            @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) load →
              (∀ (v : Fin n),
                  Lax263307Proofs.NativeSignedArithmetic.Bounded
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
                    (@NNRat.cast Rat Rat.instNNRatCast (x v))) →
                have H := Lax263307Proofs.NativeLargeResources.heightExponent b n load k h;
                ∀ (w : Nat),
                  @LE.le Nat instLENat (Lax263307Proofs.NativeUniformFlow.wordHeight n H p wp tp op) w →
                    have cs :=
                      @Lax263307.ComputedSeparators.cuts n (@Lax263307.ComputedSeparators.step n f G inst x b load k) n
                        (@Finset.univ (Fin n) (Fin.fintype n));
                    Lax808846Proofs.Reasoning.Spec
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                      (fun (σ : Lax808846Proofs.Imp.Env) =>
                        And
                          (@Lax263307Proofs.NativeSeparatorContext.Context n G inst x b load k
                            (Lax263307Proofs.NativeUniformFlow.spaceBound n H tp) σ)
                          (@LE.le Nat instLENat
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (@List.length Nat (σ.arrs "separator.pieces"))))
                      (Lax263307Proofs.NativeSeparatorOutput.command p coeff)
                      (fun (x_1 τ : Lax808846Proofs.Imp.Env) =>
                        And
                          (@Lax263307Proofs.NativeSeparatorContext.Context n G inst x b load k
                            (Lax263307Proofs.NativeUniformFlow.spaceBound n H tp) τ)
                          (And
                            (@Eq Nat (τ.vars "separator.remaining")
                              (@Lax263307Proofs.NativeMasks.mask n
                                (@Lax263307.ComputedSeparators.remaining n (@Finset.univ (Fin n) (Fin.fintype n)) cs)))
                            (And
                              (@Eq Nat (τ.vars "separator.value")
                                (@Lax263307Proofs.NativeMasks.mask n (@Lax263307.ComputedSeparators.separator n cs)))
                              (And
                                (@Eq Nat (τ.vars "separator.count")
                                  (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs))
                                (And
                                  (Lax455465Proofs.RamVirtualState.Prefix (@Lax263307Proofs.NativeCutRecords.words n cs)
                                    "separator.cuts" τ)
                                  (And
                                    (@Eq Nat (τ.vars "separator.position")
                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                        (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs)))
                                    (Lax455465Proofs.RamVirtualState.Prefix
                                      (@Lax263307Proofs.NativeCutPieces.words n cs) "separator.pieces" τ)))))))
                      (Lax263307Proofs.NativeSeparatorOutput.timeBound n H p coeff tp)) := by sorry
