-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeSeparatorProgram_exists_program_native
-- name    : Lax263307Proofs.NativeSeparatorProgram.exists_program_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:25:57.158478+00:00
-- url     : https://prove2.me/theorems/db9192a3-7dad-4b09-a3ed-db49494dd37e
-- title:
--   Execute the full native separator cut list
-- statement:
--   Let $f$ be any total function on finite word lists with the source's polynomial-time RAM realization. There exist one fixed native separator-loop program, polynomial width/time/output bounds and its polynomial coefficients, uniform over the graph, load and accuracy parameters. For a nonempty graph, positive load, bounded nonnegative rational weights and the complete native context and workspace guards, the command stores exactly the functional cut list
--   $$\mathcal L=\operatorname{cuts}(\operatorname{step}_f,G,x,b,\operatorname{load},k).$$
--   It returns the remaining-set mask, separator-union mask, list length, encoded cut records and final record position, preserving the context within the explicit loop time bound. This is an operational equality for the chosen $f$; no additional separator-quality claim is assumed here.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeSeparatorProgram.lean, theorem Lax263307Proofs.NativeSeparatorProgram.exists_program, line 20

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
namespace Lax263307Proofs.NativeSeparatorProgram
end Lax263307Proofs.NativeSeparatorProgram

theorem Lax263307Proofs.NativeSeparatorProgram.exists_program_native : ∀ (f : List Nat → List Nat),
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
                          (@Eq Nat (σ.vars "separator.remaining")
                            (@Lax263307Proofs.NativeMasks.mask n (@Finset.univ (Fin n) (Fin.fintype n)))))
                      (Lax263307Proofs.NativeSeparatorProgram.command p coeff)
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
                                  (@Eq Nat (τ.vars "separator.position")
                                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                      (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs))))))))
                      (Lax263307Proofs.NativeSeparatorProgram.timeBound n H p coeff tp)) := by sorry
