-- Prove2me | Theorems.Thm_Lax109476Proofs_RamMatrixVector_ellipsoidMulVec_spec_native
-- name    : Lax109476Proofs.RamMatrixVector.ellipsoidMulVec_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:30.696208+00:00
-- url     : https://prove2.me/theorems/6dc6805d-c851-44da-abe9-6dfa016630d8
-- title:
--   Stored ellipsoid matrix-vector multiplication
-- statement:
--   Let $A$ be a rational $n\times n$ matrix and $c$ a rational vector, with every entry of height at most $H\ge1$. Assume the stated dimension and arithmetic-cap word guards, initialized matrix and input buffers, and a zero output buffer. The bounded command computes the exact vector, preserves $A,c,n$, and has the explicit quadratic-loop instruction bound:
--
--   $$u_i=\sum_{j<n}A_{ij}c_j.$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamMatrixVector.lean, theorem ellipsoidMulVec_spec (lines 158–175)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax109476Proofs.RamMatrixVector
end Lax109476Proofs.RamMatrixVector

theorem Lax109476Proofs.RamMatrixVector.ellipsoidMulVec_spec_native : ∀ (B n H : Nat) (A : Matrix (Fin n) (Fin n) Rat) (c : Fin n → Rat),
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) H →
    (∀ (k j : Fin n), Lax109476Proofs.RationalArithmeticBounds.Height (A k j) H) →
      (∀ (j : Fin n), Lax109476Proofs.RationalArithmeticBounds.Height (c j) H) →
        @LT.lt Nat instLTNat
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n n)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            B →
          @LT.lt Nat instLTNat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    (Lax109476Proofs.RamDotProduct.cap n H) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              B →
            Lax808846Proofs.Reasoning.Spec B
              (fun (σ : Lax808846Proofs.Imp.Env) =>
                And (@Lax109476Proofs.RamMatrixRows.MatrixRows n n "ell.shape" A σ)
                  (And (Lax109476Proofs.RamRationalArrays.Represents "ell.normal" (@List.ofFn Rat n c) σ)
                    (And
                      (Lax109476Proofs.RamRationalArrays.Represents "ell.u"
                        (@List.replicate Rat n (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) σ)
                      (@Eq Nat (σ.vars "vec.n") n))))
              Lax109476Proofs.RamMatrixVector.ellipsoidMulVec
              (fun (x τ : Lax808846Proofs.Imp.Env) =>
                And
                  (Lax109476Proofs.RamRationalArrays.Represents "ell.u"
                    (@List.ofFn Rat n
                      (@Matrix.mulVec (Fin n) (Fin n) Rat
                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Rat
                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Rat
                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Rat
                              (@CommRing.toNonUnitalCommRing Rat Rat.commRing))))
                        (Fin.fintype n) A c))
                    τ)
                  (And (@Lax109476Proofs.RamMatrixRows.MatrixRows n n "ell.shape" A τ)
                    (And (Lax109476Proofs.RamRationalArrays.Represents "ell.normal" (@List.ofFn Rat n c) τ)
                      (@Eq Nat (τ.vars "vec.n") n))))
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                    (@OfNat.ofNat Nat (nat_lit 144) (instOfNatNat (nat_lit 144)))
                                    (Lax109476Proofs.RamDotProduct.cap n H).size)
                                  (@OfNat.ofNat Nat (nat_lit 216) (instOfNatNat (nat_lit 216))))
                                (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                              n)
                            (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))
                        (@OfNat.ofNat Nat (nat_lit 21) (instOfNatNat (nat_lit 21))))
                      (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  n)
                (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) := by sorry
