-- Prove2me | Theorems.Thm_Lax263307Proofs_ProjectedOracle_run_correct_native
-- name    : Lax263307Proofs.ProjectedOracle.run_correct_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:35.076073+00:00
-- url     : https://prove2.me/theorems/b06168f7-81dd-4e26-8835-96a8c68f4421
-- title:
--   Correctness of the rational projected round-or-cut oracle
-- statement:
--   Fix a positive-order graph, a positive structural constant, precision denominator at least four, and the other published algorithm parameters. Assume the LP function always returns valid certificates and that the near branch, including its supplied child procedure, satisfies its complete correctness contract. For every rational moment-coordinate query center $x$, the actual functional projected procedure returns a correct rounded-oracle reply:
--
--   $$\operatorname{CorrectReply}_{G,k,h,a,K,B,D}\bigl(x,\operatorname{ProjectedOracle}(x)\bigr).$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/ProjectedOracle.lean, theorem run_correct (lines 63–194)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax263307Proofs.ProjectedOracle
end Lax263307Proofs.ProjectedOracle

theorem Lax263307Proofs.ProjectedOracle.run_correct_native : ∀ {n : Nat} (lp flow : List Nat → List Nat) (a K B D : Nat) (G : SimpleGraph (Fin n))
  [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (k h : Nat),
  @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) K →
    @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
      @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) D →
        (∀ (m N : Nat) (P : Lax109476.LinearProgram.Program Rat m N),
            @Lax109476.RationalCertificates.IsValidCertificate m N P (@Lax263307.RegisteredLP.certificate m N lp P)) →
          ∀ (child : Finset (Fin n) → Nat → Option (Finset (Fin n))),
            (∀ (y : Lax263307.RationalConditioning.RationalVector n (Lax263307.AlgorithmParameters.level a K B n D)),
                @Lax263307.LinearRelaxation.IsFeasible n G k (Lax263307.AlgorithmParameters.level a K B n D)
                    (@Lax263307.RationalConditioning.realVector n (Lax263307.AlgorithmParameters.level a K B n D) y) →
                  ∀ (x : Lax263307.LinearRelaxation.MomentVector n (Lax263307.AlgorithmParameters.level a K B n D)),
                    (∀ (T : Lax263307.LinearRelaxation.Coordinate n (Lax263307.AlgorithmParameters.level a K B n D)),
                        @LE.le Real Real.instLE
                          (@abs Real Real.lattice Real.instAddGroup
                            (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (x T)
                              (@Lax263307.RationalConditioning.realVector n
                                (Lax263307.AlgorithmParameters.level a K B n D) y T)))
                          (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                            (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                              (@Rat.cast Real Real.instRatCast (Lax263307.AlgorithmParameters.momentFloor a K B n D))
                              (@HPow.hPow Real Nat Real
                                (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
                                (@HDiv.hDiv Real Real Real
                                  (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                  (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                                  (@Nat.cast Real Real.instNatCast D))
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                              (@OfNat.ofNat Real (nat_lit 32)
                                (@instOfNatAtLeastTwo Real (nat_lit 32) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                                    (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                              (@HPow.hPow Real Nat Real
                                (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
                                (@Nat.cast Real Real.instNatCast n)
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) →
                      @Lax263307.NearOracle.Correct n (Lax263307.AlgorithmParameters.level a K B n D) G k h D
                        (@Rat.cast Real Real.instRatCast (Lax263307.AlgorithmParameters.momentFloor a K B n D)) x
                        (@Lax263307.NearOracle.run n flow a K B D G inst k y child)) →
              ∀ (center : Lax263307.MomentLP.Index n (Lax263307.AlgorithmParameters.level a K B n D) → Rat),
                @Lax263307.ProjectedOracle.Correct n G k h a K B D center
                  (@Lax263307.ProjectedOracle.run n lp flow a K B D G inst k child center) := by sorry
