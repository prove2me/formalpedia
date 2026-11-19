-- Prove2me | Theorems.Thm_Lax455465Proofs_RamRegionSetup_command_spec_native
-- name    : Lax455465Proofs.RamRegionSetup.command_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:23.577211+00:00
-- url     : https://prove2.me/theorems/5040b8a5-8587-4098-803c-2fd0a7c57cb5
-- title:
--   Construct a bounded region query from stored metric data
-- statement:
--   Fix a rational network instance, its rational metric, the seed and threshold data, and the active-set/history state appearing in this interface. Assume its complete coefficient-height, dimension, positivity, word-size and allocated-storage guards. The fixed command implements the chosen region query and its stored context, with the explicit instruction bound from the source:
--
--   $$\mathrm{Spec}_B(\mathrm{SetupInput},c_{\rm setup},\mathrm{StoredQuery},T_{\rm setup}).$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRegionSetup.lean, theorem command_spec (lines 79–144)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax455465Proofs.RamRegionSetup
end Lax455465Proofs.RamRegionSetup

theorem Lax455465Proofs.RamRegionSetup.command_spec_native : ∀ (B M H : Nat) {n : Nat} (weights : Fin n → NNRat) (capacity length : Lax455465Proofs.MetricMatrix.Matrix n)
  (root : Fin n) (seed beta delta : NNRat) (k : Nat),
  @LE.le Nat instLENat k M →
    @LT.lt Nat instLTNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        B →
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
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
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
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)))
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                B →
              (∀ (u v : Fin n), Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast (length u v))) →
                Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast delta) →
                  Lax455465Proofs.LpInputSize.Height M
                      (@NNRat.cast Rat Rat.instNNRatCast
                        (@HDiv.hDiv NNRat NNRat NNRat (@instHDiv NNRat NNRat.instDiv) delta
                          (@Nat.cast NNRat
                            (@AddMonoidWithOne.toNatCast NNRat
                              (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
                                (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
                                  (@Semiring.toNonAssocSemiring NNRat
                                    (@DivisionSemiring.toSemiring NNRat
                                      (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
                            k))) →
                    (∀ (i : Nat)
                        (hi :
                          @LT.lt Nat instLTNat i
                            (@List.length NNRat
                              (@Lax455465Proofs.RadiusData.candidates n (length root) (fun (v : Fin n) => length v root)
                                k delta))),
                        @Lax455465Proofs.RegionQueryHeight.Bounds n
                          (@Lax455465Proofs.RadiusSearchData.atRadius n
                            (@Lax455465Proofs.RamRegionSetup.query n weights capacity length root seed beta)
                            (@GetElem.getElem (List NNRat) Nat NNRat
                              (fun (as : List NNRat) (i : Nat) => @LT.lt Nat instLTNat i (@List.length NNRat as))
                              (@List.instGetElemNatLtLength NNRat)
                              (@Lax455465Proofs.RadiusData.candidates n (length root) (fun (v : Fin n) => length v root)
                                k delta)
                              i hi))
                          H) →
                      Lax808846Proofs.Reasoning.Spec B
                        (fun (σ : Lax808846Proofs.Imp.Env) =>
                          And (@Lax455465Proofs.RamRegionSetup.Input n weights capacity length root seed beta delta k σ)
                            (Lax455465Proofs.RamRegionSetup.Room n
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                              σ))
                        Lax455465Proofs.RamRegionSetup.command
                        (fun (x τ : Lax808846Proofs.Imp.Env) =>
                          And
                            (@Lax455465Proofs.RamRadiusSearch.Context n
                              (@Lax455465Proofs.RamRegionSetup.query n weights capacity length root seed beta)
                              (@Lax455465Proofs.RadiusData.candidates n (length root) (fun (v : Fin n) => length v root)
                                k delta)
                              τ)
                            (And
                              (Lax455465Proofs.RamFind.Matches
                                (Lax455465Proofs.RamFind.first
                                  (@Lax455465Proofs.RadiusSearchData.predicate n
                                    (@Lax455465Proofs.RamRegionSetup.query n weights capacity length root seed beta)
                                    (@Lax455465Proofs.RadiusData.candidates n (length root)
                                      (fun (v : Fin n) => length v root) k delta))
                                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)))
                                τ)
                              (@Lax455465Proofs.RamSelectedRegion.Selected n
                                (@Lax455465Proofs.RamRegionSetup.query n weights capacity length root seed beta)
                                (@Lax455465Proofs.RadiusData.candidates n (length root)
                                  (fun (v : Fin n) => length v root) k delta)
                                τ)))
                        (Lax455465Proofs.RamRegionSetup.cost n k M H) := by sorry
