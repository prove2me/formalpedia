-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeRecursiveOracle_trajectory_guards_native
-- name    : Lax263307Proofs.NativeRecursiveOracle.trajectory_guards_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:02:10.739625+00:00
-- url     : https://prove2.me/theorems/d4b7b6c5-7786-4b2a-8044-680e900895a2
-- title:
--   Rational trajectory heights and positive cut directions
-- statement:
--   Let $G$ be a member of a hereditary graph class with more than one vertex, and let the functional recursive oracle satisfy its correctness contract. Suppose the accuracy denominator is at least four, the target is above the large-node cutoff, the fuel covers the recursion depth, the relaxation dimension is at most $R$, and $j\le R$. At round $j$, every center and shape entry has numerator magnitude and denominator at most $2^{80(R+1)}$. Moreover, whenever that round returns a cut normal $z$,
--   $$z^{\mathsf T}A_jz>0.$$
--   These uniform conclusions provide the exact height and positivity guards needed by the native rounded ellipsoid update.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeRecursiveOracle.lean, theorem Lax263307Proofs.NativeRecursiveOracle.trajectory_guards, line 96

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
namespace Lax263307Proofs.NativeRecursiveOracle
end Lax263307Proofs.NativeRecursiveOracle

theorem Lax263307Proofs.NativeRecursiveOracle.trajectory_guards_native : ∀ {C : Lax263307.GraphClasses.GraphClass},
  Lax263307.GraphClasses.IsHereditary C →
    ∀ {lp flow : List Nat → List Nat} {a K b : Nat},
      Lax263307Proofs.NativeRecursiveOracle.OracleCorrect C lp flow a K b →
        ∀ {n : Nat} (G : SimpleGraph (Fin n)) [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)],
          @Membership.mem (SimpleGraph (Fin n)) (Set (SimpleGraph (Fin n))) (@Set.instMembership (SimpleGraph (Fin n)))
              (C n) G →
            @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n →
              ∀ (D k fuel R j : Nat),
                @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) D →
                  @LT.lt Nat instLTNat (Lax263307.AlgorithmParameters.cutoff a K b n D) k →
                    @LE.le Nat instLENat (Lax263307.RecursionDepth.depth n)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) fuel
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                      @LE.le Nat instLENat
                          (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D)) R →
                        @LE.le Nat instLENat j R →
                          have oracle :=
                            fun (x : Nat)
                              (center :
                                Lax263307.MomentLP.Index n (Lax263307.AlgorithmParameters.level a K b n D) → Rat) =>
                            @Lax263307.ProjectedOracle.run n lp flow a K b D G inst k
                              (@Lax263307Proofs.NativeRecursiveOracle.child n lp flow a K b D fuel G inst) center;
                          And
                            (∀
                              (i l :
                                Fin (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))),
                              Lax263307.NativeRoundedStep.height
                                (@Prod.fst
                                  (Matrix
                                    (Fin
                                      (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D)))
                                    (Fin
                                      (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D)))
                                    Rat)
                                  (Fin
                                      (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D)) →
                                    Rat)
                                  (@Lax263307.RoundedOracleSearch.trajectory
                                    (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))
                                    (Finset (Fin n)) oracle j)
                                  i l)
                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                  (@OfNat.ofNat Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))
                                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) R
                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                            (And
                              (∀
                                (i :
                                  Fin (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))),
                                Lax263307.NativeRoundedStep.height
                                  (@Prod.snd
                                    (Matrix
                                      (Fin
                                        (Lax263307.MomentLP.dimension n
                                          (Lax263307.AlgorithmParameters.level a K b n D)))
                                      (Fin
                                        (Lax263307.MomentLP.dimension n
                                          (Lax263307.AlgorithmParameters.level a K b n D)))
                                      Rat)
                                    (Fin
                                        (Lax263307.MomentLP.dimension n
                                          (Lax263307.AlgorithmParameters.level a K b n D)) →
                                      Rat)
                                    (@Lax263307.RoundedOracleSearch.trajectory
                                      (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))
                                      (Finset (Fin n)) oracle j)
                                    i)
                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                    (@OfNat.ofNat Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))
                                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) R
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                              (∀
                                (normal :
                                  Fin (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D)) →
                                    Int),
                                @Eq
                                    (Lax263307.RoundedOracleSearch.Reply
                                      (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))
                                      (Finset (Fin n)))
                                    (oracle j
                                      (@Prod.snd
                                        (Matrix
                                          (Fin
                                            (Lax263307.MomentLP.dimension n
                                              (Lax263307.AlgorithmParameters.level a K b n D)))
                                          (Fin
                                            (Lax263307.MomentLP.dimension n
                                              (Lax263307.AlgorithmParameters.level a K b n D)))
                                          Rat)
                                        (Fin
                                            (Lax263307.MomentLP.dimension n
                                              (Lax263307.AlgorithmParameters.level a K b n D)) →
                                          Rat)
                                        (@Lax263307.RoundedOracleSearch.trajectory
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D))
                                          (Finset (Fin n)) oracle j)))
                                    (@Lax263307.RoundedOracleSearch.Reply.cut
                                      (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))
                                      (Finset (Fin n)) normal) →
                                  @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                    (@dotProduct
                                      (Fin
                                        (Lax263307.MomentLP.dimension n
                                          (Lax263307.AlgorithmParameters.level a K b n D)))
                                      Rat
                                      (Fin.fintype
                                        (Lax263307.MomentLP.dimension n
                                          (Lax263307.AlgorithmParameters.level a K b n D)))
                                      Rat.instMul Rat.addCommMonoid
                                      (@Lax263307.RoundedOracleSearch.rationalNormal
                                        (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))
                                        normal)
                                      (@Matrix.mulVec
                                        (Fin
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D)))
                                        (Fin
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D)))
                                        Rat
                                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Rat
                                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Rat
                                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Rat
                                              (@CommRing.toNonUnitalCommRing Rat Rat.commRing))))
                                        (Fin.fintype
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D)))
                                        (@Prod.fst
                                          (Matrix
                                            (Fin
                                              (Lax263307.MomentLP.dimension n
                                                (Lax263307.AlgorithmParameters.level a K b n D)))
                                            (Fin
                                              (Lax263307.MomentLP.dimension n
                                                (Lax263307.AlgorithmParameters.level a K b n D)))
                                            Rat)
                                          (Fin
                                              (Lax263307.MomentLP.dimension n
                                                (Lax263307.AlgorithmParameters.level a K b n D)) →
                                            Rat)
                                          (@Lax263307.RoundedOracleSearch.trajectory
                                            (Lax263307.MomentLP.dimension n
                                              (Lax263307.AlgorithmParameters.level a K b n D))
                                            (Finset (Fin n)) oracle j))
                                        (@Lax263307.RoundedOracleSearch.rationalNormal
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D))
                                          normal))))) := by sorry
