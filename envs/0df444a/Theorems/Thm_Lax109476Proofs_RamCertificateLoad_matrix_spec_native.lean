-- Prove2me | Theorems.Thm_Lax109476Proofs_RamCertificateLoad_matrix_spec_native
-- name    : Lax109476Proofs.RamCertificateLoad.matrix_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:26:12.871594+00:00
-- url     : https://prove2.me/theorems/ad6e4034-c0ee-4d99-83d3-57f73976412b
-- title:
--   Read a stored integer matrix coefficient as a rational
-- statement:
--   Let $P$ be a stored integer program with $m$ rows and $n$ columns, and let $i<m$, $j<n$. Suppose $1\le M<B$, the matrix coefficient has magnitude at most $M$, and $mn+m+n+4<B$. The fixed coefficient reader preserves the source storage and returns the signed rational value
--   $$q_{\rm out}=A_{ij}$$
--   in at most $21$ instructions. The query registers initially specify $i,j$.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamCertificateLoad.lean, theorem Lax109476Proofs.RamCertificateLoad.matrix_spec, line 17

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
namespace Lax109476Proofs.RamCertificateLoad
end Lax109476Proofs.RamCertificateLoad

theorem Lax109476Proofs.RamCertificateLoad.matrix_spec_native : ∀ (B M m n : Nat) (P : Lax109476.LinearProgram.Program Int m n) (i : Fin m) (j : Fin n),
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
    @LT.lt Nat instLTNat M B →
      @LT.lt Nat instLTNat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) m n)
                m)
              n)
            (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          B →
        @LE.le Nat instLENat (@Lax109476.LinearProgram.Program.A Int m n P i j).natAbs M →
          Lax808846Proofs.Reasoning.Spec B
            (fun (σ : Lax808846Proofs.Imp.Env) =>
              And (@Lax109476Proofs.RamCertificateSource.Data m n P σ)
                (And (@Eq Nat (σ.vars "query.a.row") (@Fin.val m i)) (@Eq Nat (σ.vars "query.a.col") (@Fin.val n j))))
            Lax109476Proofs.RamCertificateLoad.matrix
            (fun (x τ : Lax808846Proofs.Imp.Env) =>
              And (@Lax109476Proofs.RamCertificateSource.Data m n P τ)
                (Lax109476Proofs.RamRational.FractionOutput
                  (@Int.cast Rat Rat.instIntCast (@Lax109476.LinearProgram.Program.A Int m n P i j)) τ))
            (@OfNat.ofNat Nat (nat_lit 21) (instOfNatNat (nat_lit 21))) := by sorry
