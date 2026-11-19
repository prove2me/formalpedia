-- Prove2me | Theorems.Thm_Lax455465Proofs_RamSelectedRegion_command_spec_native
-- name    : Lax455465Proofs.RamSelectedRegion.command_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:25:56.444617+00:00
-- url     : https://prove2.me/theorems/e1bc0887-87fc-46a0-80b1-9d500b47ef66
-- title:
--   Select the first valid stored region radius
-- statement:
--   Let a finite list of nonnegative rational candidate radii and a rational region query be stored in their complete native context. Suppose every radius query satisfies the published height-$H$ bound, and the matrix, vertex, radius-position and word guards hold. The fixed selector retains that context and returns the exact first successful radius, or the no-success outcome:
--   $$j=\min\{i<r:\operatorname{predicate}(q,\rho_i)\},$$
--   with the corresponding selected-query result when the set is nonempty. Its instruction bound is $(T_{\rm query}(n,H)+38)r+T_{\rm query}(n,H)+40$.
-- source:
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamSelectedRegion.lean, theorem Lax455465Proofs.RamSelectedRegion.command_spec, line 21

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
namespace Lax455465Proofs.RamSelectedRegion
end Lax455465Proofs.RamSelectedRegion

theorem Lax455465Proofs.RamSelectedRegion.command_spec_native : ∀ (B H : Nat) {n : Nat} (q : Lax455465Proofs.RegionQueryData.Query n) (radii : List NNRat),
  (∀ (i : Nat) (hi : @LT.lt Nat instLTNat i (@List.length NNRat radii)),
      @Lax455465Proofs.RegionQueryHeight.Bounds n
        (@Lax455465Proofs.RadiusSearchData.atRadius n q
          (@GetElem.getElem (List NNRat) Nat NNRat
            (fun (as : List NNRat) (i : Nat) => @LT.lt Nat instLTNat i (@List.length NNRat as))
            (@List.instGetElemNatLtLength NNRat) radii i hi))
        H) →
    @LT.lt Nat instLTNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H)
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        B →
      @LT.lt Nat instLTNat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          B →
        @LT.lt Nat instLTNat
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            B →
          @LT.lt Nat instLTNat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length NNRat radii))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              B →
            Lax808846Proofs.Reasoning.Spec B (@Lax455465Proofs.RamRadiusSearch.Context n q radii)
              Lax455465Proofs.RamSelectedRegion.command
              (fun (x τ : Lax808846Proofs.Imp.Env) =>
                And (@Lax455465Proofs.RamRadiusSearch.Context n q radii τ)
                  (And
                    (Lax455465Proofs.RamFind.Matches
                      (Lax455465Proofs.RamFind.first (@Lax455465Proofs.RadiusSearchData.predicate n q radii)
                        (@List.length NNRat radii))
                      τ)
                    (@Lax455465Proofs.RamSelectedRegion.Selected n q radii τ)))
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (Lax455465Proofs.RamRadiusSearch.queryCost n H)
                      (@OfNat.ofNat Nat (nat_lit 38) (instOfNatNat (nat_lit 38))))
                    (@List.length NNRat radii))
                  (Lax455465Proofs.RamRadiusSearch.queryCost n H))
                (@OfNat.ofNat Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))) := by sorry
