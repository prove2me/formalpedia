-- Prove2me | Theorems.Thm_Lax109476Proofs_RamPairSelector_selectEntry_spec_native
-- name    : Lax109476Proofs.RamPairSelector.selectEntry_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:35.201314+00:00
-- url     : https://prove2.me/theorems/be5ff4f9-b558-47ce-ab1e-711de4eaf03c
-- title:
--   Read a coefficient of the primal-dual certificate system
-- statement:
--   Let $P$ be an integer LP with $m$ constraints and $n$ variables, whose stored coefficients meet the published bound $M$. The joint primal-dual feasibility system has $m+n+2$ rows and $n+m$ columns. For each valid requested index, under the stated source-storage and host-word guards, the selector command reads its matrix coefficient into the signed rational result registers:
--
--   $$\mathrm{fraction}_{\rm out}=A^\star_{ij}.$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamPairSelector.lean, theorem selectEntry_spec (lines 36–103)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax109476Proofs.RamPairSelector
end Lax109476Proofs.RamPairSelector

theorem Lax109476Proofs.RamPairSelector.selectEntry_spec_native : ∀ (B M m n : Nat) (P : Lax109476.LinearProgram.Program Int m n)
  (i :
    Fin
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (j : Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n m)),
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
    @LT.lt Nat instLTNat M B →
      @LT.lt Nat instLTNat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) m n)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
            (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          B →
        (∀ (r : Fin m) (s : Fin n), @LE.le Nat instLENat (@Lax109476.LinearProgram.Program.A Int m n P r s).natAbs M) →
          (∀ (r : Fin m), @LE.le Nat instLENat (@Lax109476.LinearProgram.Program.b Int m n P r).natAbs M) →
            (∀ (s : Fin n), @LE.le Nat instLENat (@Lax109476.LinearProgram.Program.c Int m n P s).natAbs M) →
              Lax808846Proofs.Reasoning.Spec B
                (fun (σ : Lax808846Proofs.Imp.Env) =>
                  And (@Lax109476Proofs.RamCertificateSource.Data m n P σ)
                    (And
                      (@Eq Nat (σ.vars "query.row")
                        (@Fin.val
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          i))
                      (@Eq Nat (σ.vars "query.col")
                        (@Fin.val (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n m) j))))
                Lax109476Proofs.RamPairSelector.selectEntry
                (fun (x τ : Lax808846Proofs.Imp.Env) =>
                  And (@Lax109476Proofs.RamCertificateSource.Data m n P τ)
                    (Lax109476Proofs.RamRational.FractionOutput
                      (@Int.cast Rat Rat.instIntCast (@Lax109476Proofs.CertificateFamilyEntries.pairEntry m n P i j))
                      τ))
                (@OfNat.ofNat Nat (nat_lit 72) (instOfNatNat (nat_lit 72))) := by sorry
