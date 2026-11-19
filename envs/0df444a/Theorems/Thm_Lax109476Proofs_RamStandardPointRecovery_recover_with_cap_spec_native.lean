-- Prove2me | Theorems.Thm_Lax109476Proofs_RamStandardPointRecovery_recover_with_cap_spec_native
-- name    : Lax109476Proofs.RamStandardPointRecovery.recover_with_cap_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:39.483619+00:00
-- url     : https://prove2.me/theorems/eaacedb9-02c7-401a-ae33-cc4d52d9c57b
-- title:
--   Exact native recovery of a capped standard-form point
-- statement:
--   Let $Cz=b$ be a feasible integer linear system with the specified coefficient-height bound. Assume the stated coordinate cap, precision, reconstruction-depth, word-width and initialized-workspace guards. The actual capped-recovery command returns a rational vector satisfying the equations exactly and retains the complete stored recovery-state predicate and coordinate-height conclusions:
--
--   $$Cz=b.$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamStandardPointRecovery.lean, theorem recover_with_cap_spec (lines 19–68)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax109476Proofs.RamStandardPointRecovery
end Lax109476Proofs.RamStandardPointRecovery

theorem Lax109476Proofs.RamStandardPointRecovery.recover_with_cap_spec_native : ∀ (m n H S K N w D : Nat) (C : Matrix (Fin m) (Fin n) Int) (b : Fin m → Int),
  (∀ (i : Fin m) (j : Fin n), @LE.le Nat instLENat (C i j).natAbs H) →
    (∀ (i : Fin m), @LE.le Nat instLENat (b i).natAbs H) →
      @LE.le Nat instLENat H
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) S) →
        @LE.le Nat instLENat (Lax109476Proofs.LexicographicBounds.coordinateCap m n H) D →
          @LE.le Nat instLENat D.size K →
            @LE.le Nat instLENat
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) K)
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                S →
              @LE.le Nat instLENat
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (Lax109476Proofs.RamRationalReconstruction.depthBound S)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  N →
                @LE.le Nat instLENat
                    (Lax109476Proofs.RamPointRecoveryBounds.wordWidth
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m m) n S)
                    w →
                  (∃ (x : Fin n → Rat),
                      @Lax109476Proofs.LexicographicSupport.Feasible m n
                        (@Matrix.map (Fin m) (Fin n) Int Rat C fun (z : Int) => @Int.cast Rat Rat.instIntCast z)
                        (fun (i : Fin m) => @Int.cast Rat Rat.instIntCast (b i)) x) →
                    Lax808846Proofs.Reasoning.Spec
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                      (fun (σ : Lax808846Proofs.Imp.Env) =>
                        And
                          (@Lax109476Proofs.RamPointInitialization.Base
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m m) n
                            (@Lax109476Proofs.RamStandardPointRecovery.program m n C b) σ)
                          (And
                            (Lax109476Proofs.RamRecoveryThreshold.Workspace
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m m) n σ)
                            (And (Lax109476Proofs.RamEllipsoidStep.Extents "point.x" n σ)
                              (And (@Eq Nat (σ.vars "minimum.bound") D)
                                (@Eq Nat (@List.length Nat (σ.arrs "cf.stack")) N)))))
                      Lax109476Proofs.RamPointInitialization.recover
                      (fun (x τ : Lax808846Proofs.Imp.Env) =>
                        ∃ (x : Fin n → Rat),
                          And
                            (@Lax109476Proofs.RamRecoveryThreshold.Persistent
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m m) n
                              (@Lax109476Proofs.RamStandardPointRecovery.program m n C b) x n τ)
                            (And
                              (@Lax109476Proofs.LexicographicSupport.Feasible m n
                                (@Matrix.map (Fin m) (Fin n) Int Rat C fun (z : Int) => @Int.cast Rat Rat.instIntCast z)
                                (fun (i : Fin m) => @Int.cast Rat Rat.instIntCast (b i)) x)
                              (∀ (j : Fin n),
                                Lax109476Proofs.RationalArithmeticBounds.Height (x j)
                                  (Lax109476Proofs.LexicographicBounds.coordinateCap m n H))))
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 33) (instOfNatNat (nat_lit 33))) n)
                          (@OfNat.ofNat Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
                        (Lax109476Proofs.RamPointRecoveryBounds.instructionBound
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m m) n S K)) := by sorry
