-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeOracleCutHeight_normal_height_native
-- name    : Lax263307Proofs.NativeOracleCutHeight.normal_height_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:02:04.637037+00:00
-- url     : https://prove2.me/theorems/6b3cef83-5355-40cd-bebc-3b45dfd14f86
-- title:
--   Bound the rational normal returned by a selected native oracle
-- statement:
--   Let a selected encoded LP solver and a correct separator function be fixed for a graph class, with positive structural constants. Let $G$ belong to the class, let $D\ge4$ and let its target exceed the large-node cutoff. Suppose the graph order, target, relaxation level and dimension are bounded by $R$, and the queried center has the source’s height bound $80(R+1)$. For any child-answer function, if the round oracle returns a cut normal $z$, then every coordinate of its rational interpretation satisfies
--   $$|\operatorname{num}(z_i)|,\ \operatorname{den}(z_i)\le2^{H(\operatorname{solverWidth},R)}.$$
--   Here $H$ is the explicit rounded-normal height function defined in the published interface. The conclusion is uniform in the round index and child-answer function.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeOracleCutHeight.lean, theorem Lax263307Proofs.NativeOracleCutHeight.normal_height, line 51

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
namespace Lax263307Proofs.NativeOracleCutHeight
end Lax263307Proofs.NativeOracleCutHeight

theorem Lax263307Proofs.NativeOracleCutHeight.normal_height_native : ∀ {C : Lax263307.GraphClasses.GraphClass} {lp flow : List Nat → List Nat} {a K b : Nat},
  Lax263307Proofs.NearOracle.SeparatorCorrect C flow a K b →
    @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) K →
      @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b →
        Lax263307Proofs.NativeEncodedLP.Encoded lp →
          ∀ (selected : Lax263307Proofs.NativeSelectedLP.Program lp) {n : Nat} (G : SimpleGraph (Fin n))
            [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)],
            @Membership.mem (SimpleGraph (Fin n)) (Set (SimpleGraph (Fin n)))
                (@Set.instMembership (SimpleGraph (Fin n))) (C n) G →
              ∀ (D k R F j : Nat),
                @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
                  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) D →
                    @LT.lt Nat instLTNat (Lax263307.AlgorithmParameters.cutoff a K b n D) k →
                      @LE.le Nat instLENat n R →
                        @LE.le Nat instLENat k R →
                          @LE.le Nat instLENat (Lax263307.AlgorithmParameters.level a K b n D) R →
                            @LE.le Nat instLENat
                                (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D)) R →
                              ∀
                                (center :
                                  Lax263307.MomentLP.Index n (Lax263307.AlgorithmParameters.level a K b n D) → Rat),
                                (∀ (i : Lax263307.MomentLP.Index n (Lax263307.AlgorithmParameters.level a K b n D)),
                                    Lax263307.NativeRoundedStep.height (center i)
                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                        (@OfNat.ofNat Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))
                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) R
                                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                                  ∀
                                    (child :
                                      (A : Finset (Fin n)) → Nat → Option (Finset (Fin (@Finset.card (Fin n) A))))
                                    (normal :
                                      Fin
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D)) →
                                        Int),
                                    @Eq
                                        (Lax263307.RoundedOracleSearch.Reply
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D))
                                          (Finset (Fin n)))
                                        (@Lax263307Proofs.NativeOracleRounds.oracle n
                                          (Lax263307.AlgorithmParameters.level a K b n D) lp flow G inst D k
                                          (Lax263307.AlgorithmParameters.sparsity a K b n D) b
                                          (Lax263307.AlgorithmParameters.load b n D) F child j center)
                                        (@Lax263307.RoundedOracleSearch.Reply.cut
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D))
                                          (Finset (Fin n)) normal) →
                                      ∀
                                        (i :
                                          Fin
                                            (Lax263307.MomentLP.dimension n
                                              (Lax263307.AlgorithmParameters.level a K b n D))),
                                        Lax263307.NativeRoundedStep.height
                                          (@Lax263307.RoundedOracleSearch.rationalNormal
                                            (Lax263307.MomentLP.dimension n
                                              (Lax263307.AlgorithmParameters.level a K b n D))
                                            normal i)
                                          (Lax263307Proofs.NativeOraclePrecision.roundedHeight
                                            (@Lax263307Proofs.NativeSelectedLP.Program.width lp selected) R) := by sorry
