-- Prove2me | Theorems.Thm_Lax109476Proofs_RamPairSelector_selectBound_spec_native
-- name    : Lax109476Proofs.RamPairSelector.selectBound_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:26.903221+00:00
-- url     : https://prove2.me/theorems/bd02fdb5-4836-4304-90bc-512a3fc8e6e2
-- title:
--   Read a bound of the primal-dual certificate system
-- statement:
--   Let $P$ be an integer LP with $m$ constraints and $n$ variables, whose stored coefficients meet the published bound $M$. The joint primal-dual feasibility system has $m+n+2$ rows and $n+m$ columns. For each valid requested index, under the stated source-storage and host-word guards, the selector command reads its right-hand-side entry into the signed rational result registers:
--
--   $$\mathrm{fraction}_{\rm out}=b^\star_i.$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamPairSelector.lean, theorem selectBound_spec (lines 113–151)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax109476Proofs.RamPairSelector
end Lax109476Proofs.RamPairSelector

theorem Lax109476Proofs.RamPairSelector.selectBound_spec_native : ∀ (B M m n : Nat) (P : Lax109476.LinearProgram.Program Int m n)
  (i :
    Fin
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))),
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
    @LT.lt Nat instLTNat M B →
      @LT.lt Nat instLTNat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m n)
            (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          B →
        (∀ (r : Fin m), @LE.le Nat instLENat (@Lax109476.LinearProgram.Program.b Int m n P r).natAbs M) →
          (∀ (s : Fin n), @LE.le Nat instLENat (@Lax109476.LinearProgram.Program.c Int m n P s).natAbs M) →
            Lax808846Proofs.Reasoning.Spec B
              (fun (σ : Lax808846Proofs.Imp.Env) =>
                And (@Lax109476Proofs.RamCertificateSource.Data m n P σ)
                  (@Eq Nat (σ.vars "query.row")
                    (@Fin.val
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      i)))
              Lax109476Proofs.RamPairSelector.selectBound
              (fun (x τ : Lax808846Proofs.Imp.Env) =>
                And (@Lax109476Proofs.RamCertificateSource.Data m n P τ)
                  (Lax109476Proofs.RamRational.FractionOutput
                    (@Int.cast Rat Rat.instIntCast (@Lax109476Proofs.CertificateFamilyEntries.pairRhs m n P i)) τ))
              (@OfNat.ofNat Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) := by sorry
