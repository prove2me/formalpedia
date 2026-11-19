-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeMomentEncodingHeight_program_words_native
-- name    : Lax263307Proofs.NativeMomentEncodingHeight.program_words_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:38:12.055198+00:00
-- url     : https://prove2.me/theorems/0f8ddab1-c499-4186-9462-32322756948c
-- title:
--   Polynomial height of every moment-program word
-- statement:
--   For a finite graph $G$ of order $n$, target $k$ and moment level $r$, every word $z$ in the actual rational encoding of its moment linear program satisfies
--   $$z<2^{100s(n,k,r)^3+10}.$$
--   Here $s$ is the native moment-constructor size parameter. The bound includes coefficients, dimensions and all encoded metadata.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeMomentEncodingHeight.lean#L16

import Definitions.Def_EdgeSublinearMWIS_Main_NativeNextInterfaces
namespace Lax263307Proofs.NativeMomentEncodingHeight
end Lax263307Proofs.NativeMomentEncodingHeight

theorem Lax263307Proofs.NativeMomentEncodingHeight.program_words_native : ∀ {n : Nat} (G : SimpleGraph (Fin n)) [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (k r z : Nat),
  @Membership.mem Nat (List Nat) (@List.instMembership Nat)
      (@Lax109476.RationalEncoding.encodeProgram (Lax263307.MomentLP.rowCount n r) (Lax263307.MomentLP.dimension n r)
        (@Lax263307.MomentLP.program n G inst k r))
      z →
    @LT.lt Nat instLTNat z
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lax263307Proofs.NativeMomentEncodingHeight.height n k r)) := by sorry
