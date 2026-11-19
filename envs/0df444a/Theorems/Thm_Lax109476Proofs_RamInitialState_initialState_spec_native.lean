-- Prove2me | Theorems.Thm_Lax109476Proofs_RamInitialState_initialState_spec_native
-- name    : Lax109476Proofs.RamInitialState.initialState_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:02:02.41989+00:00
-- url     : https://prove2.me/theorems/e2b6669a-80f7-49fa-8ae3-c5240cd09e36
-- title:
--   Initialize the stored rational ellipsoid state
-- statement:
--   Let $n$ be a natural dimension and suppose $n<B$, $n^2<B$ and $1<B$. From the complete center, shape and ellipsoid workspace extents, with the dimension register equal to $n$, the fixed initialization command stores
--   $$c_0=0,\qquad A_0=I_n,\qquad k_0=0.$$
--   It retains the workspace and dimension and runs in at most $33n+76n^2+56$ instructions. The empty dimension is included under the same guards.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamInitialState.lean, theorem Lax109476Proofs.RamInitialState.initialState_spec, line 134

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
namespace Lax109476Proofs.RamInitialState
end Lax109476Proofs.RamInitialState

theorem Lax109476Proofs.RamInitialState.initialState_spec_native : ∀ (B n : Nat),
  @LT.lt Nat instLTNat n B →
    @LT.lt Nat instLTNat (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n) B →
      @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) B →
        Lax808846Proofs.Reasoning.Spec B
          (fun (σ : Lax808846Proofs.Imp.Env) =>
            And (Lax109476Proofs.RamEllipsoidStep.Extents "ell.center" n σ)
              (And
                (Lax109476Proofs.RamEllipsoidStep.Extents "ell.shape"
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n) σ)
                (And (Lax109476Proofs.RamEllipsoidStep.Workspace n σ) (@Eq Nat (σ.vars "vec.n") n))))
          Lax109476Proofs.RamInitialState.initialState
          (fun (x τ : Lax808846Proofs.Imp.Env) =>
            And
              (Lax109476Proofs.RamRationalArrays.Represents "ell.center"
                (@List.ofFn Rat n
                  (@OfNat.ofNat (Fin n → Rat) (nat_lit 0)
                    (@Zero.toOfNat0 (Fin n → Rat)
                      (@Pi.instZero (Fin n) (fun (a : Fin n) => Rat) fun (i : Fin n) =>
                        @MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring)))))
                τ)
              (And
                (Lax109476Proofs.RamRationalArrays.Represents "ell.shape"
                  (@Lax109476Proofs.RamMatrixStorage.flatten n n
                    (@OfNat.ofNat (Matrix (Fin n) (Fin n) Rat) (nat_lit 1)
                      (@One.toOfNat1 (Matrix (Fin n) (Fin n) Rat)
                        (@Matrix.one (Fin n) Rat (instDecidableEqFin n)
                          (@MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring))
                          (@AddMonoidWithOne.toOne Rat
                            (@AddGroupWithOne.toAddMonoidWithOne Rat
                              (@Ring.toAddGroupWithOne Rat (@DivisionRing.toRing Rat Rat.instDivisionRing))))))))
                  τ)
                (And (Lax109476Proofs.RamEllipsoidStep.Workspace n τ)
                  (And (@Eq Nat (τ.vars "vec.n") n)
                    (@Eq Nat (τ.vars "iter.k") (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                (@OfNat.ofNat Nat (nat_lit 33) (instOfNatNat (nat_lit 33))) n)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                (@OfNat.ofNat Nat (nat_lit 76) (instOfNatNat (nat_lit 76)))
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)))
            (@OfNat.ofNat Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))) := by sorry
