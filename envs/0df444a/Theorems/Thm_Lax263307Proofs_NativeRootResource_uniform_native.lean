-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeRootResource_uniform_native
-- name    : Lax263307Proofs.NativeRootResource.uniform_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:31.656799+00:00
-- url     : https://prove2.me/theorems/b5734e8d-3cb0-4e80-bdce-43c0650ce890
-- title:
--   One quasipolynomial resource envelope for every child order
-- statement:
--   Fix natural structural parameters $a,K,b$ with $K>0$. There are positive natural constants $C,d$, chosen before all orders and precision denominators, such that for every $D>0$ and $0<m\le n$ the child resource demand is bounded by the root envelope. If $h(n)$ is the published integer logarithmic parameter, then
--
--   $$\operatorname{resource}(a,K,b,m,D)\le 2^{C(Dh(n))^d}.$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeRootResource.lean, theorem uniform (lines 21–27)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax263307Proofs.NativeRootResource
end Lax263307Proofs.NativeRootResource

theorem Lax263307Proofs.NativeRootResource.uniform_native : ∀ (a K b : Nat),
  @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) K →
    ∃ (C : Nat) (d : Nat),
      And (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) C)
        (And (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d)
          (∀ (n D m : Nat),
            @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) D →
              @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
                @LE.le Nat instLENat m n →
                  @LE.le Nat instLENat (Lax263307.ParameterResources.resource a K b m D)
                    (Lax263307Proofs.NativeRootResource.envelope C d n D))) := by sorry
