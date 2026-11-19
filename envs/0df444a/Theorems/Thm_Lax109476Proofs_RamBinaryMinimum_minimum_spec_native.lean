-- Prove2me | Theorems.Thm_Lax109476Proofs_RamBinaryMinimum_minimum_spec_native
-- name    : Lax109476Proofs.RamBinaryMinimum.minimum_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:02:24.775041+00:00
-- url     : https://prove2.me/theorems/dc4723f6-ebe1-42d2-a750-415aea5a1781
-- title:
--   Bounded native bisection and rational reconstruction
-- statement:
--   Let $q:\mathbb Q\to\{0,1\}$ be any Boolean rational query and suppose a fixed query command realizes it at every permitted midpoint, preserves the full context and required bisection fields, and uses at most $T_q$ instructions. Assume the published arithmetic, interval-height, denominator, reconstruction-stack and word-width guards with parameters $S,N,w,D,M$. The native minimum routine returns exactly the functional bounded bisection-and-reconstruction result:
--   $$\operatorname{out}=\operatorname{minimum}(q,D).$$
--   It preserves the context and has instruction bound $(144\operatorname{size}(M)+342+T_q)\operatorname{steps}(D)+12\operatorname{size}(D)+T_{\rm reconstruct}(S)+48$. This operational statement does not assume monotonicity of the Boolean query.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamBinaryMinimum.lean, theorem Lax109476Proofs.RamBinaryMinimum.minimum_spec, line 93

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
namespace Lax109476Proofs.RamBinaryMinimum
end Lax109476Proofs.RamBinaryMinimum

theorem Lax109476Proofs.RamBinaryMinimum.minimum_spec_native : ∀ (S N w D M queryCost : Nat) (query : Rat → Bool) (queryCom : Lax808846Proofs.Imp.Com)
  (Q : Lax808846Proofs.Imp.Env → Prop),
  @LT.lt Nat instLTNat
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w) →
    @LT.lt Nat instLTNat (Lax109476Proofs.BinaryOptimization.steps D)
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w) →
      @LE.le Nat instLENat
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) D
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lax109476Proofs.BinaryOptimization.steps D)))
          M →
        @LE.le Nat instLENat M
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) S) →
          @LE.le Nat instLENat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (Lax109476Proofs.RamRationalReconstruction.depthBound S)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              N →
            @LE.le Nat instLENat (Lax109476Proofs.RamRationalReconstruction.wordWidth S) w →
              @LT.lt Nat instLTNat D
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w) →
                (∀ (t : Rat),
                    Lax109476Proofs.RationalArithmeticBounds.Height t
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                          (@HPow.hPow Nat Nat Nat
                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                      Lax808846Proofs.Reasoning.Spec
                        (@HPow.hPow Nat Nat Nat
                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                        (fun (σ : Lax808846Proofs.Imp.Env) =>
                          And (Q σ) (Lax109476Proofs.RamRationalScalars.Value "bisect.mid" t σ))
                        queryCom
                        (fun (x τ : Lax808846Proofs.Imp.Env) =>
                          And (Q τ)
                            (@Eq (Option Bool)
                              (Lax808846Proofs.Imp.Cond.evalB
                                (@HPow.hPow Nat Nat Nat
                                  (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                Lax109476Proofs.RamBisectionCommit.condition τ)
                              (@Option.some Bool (query t))))
                        queryCost) →
                  (∀ (x : String),
                      @Membership.mem String (List String) (@List.instMembership String)
                          Lax109476Proofs.RamBisectionLoop.fields x →
                        x ∉ queryCom.wvars) →
                    "minimum.bound" ∉ queryCom.wvars →
                      Lax109476Proofs.RamBisectionLoop.preserves
                          (@HPow.hPow Nat Nat Nat
                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                          Q Lax109476Proofs.RamRationalMidpoint.midpoint →
                        Lax109476Proofs.RamBisectionLoop.preserves
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                            Q
                            (Lax109476Proofs.RamBisectionCommit.commit.seq Lax109476Proofs.RamBisectionLoop.increment) →
                          (∀ (σ : Lax808846Proofs.Imp.Env),
                              Q σ → Q (σ.setVar "bisect.i" (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
                            Lax109476Proofs.RamBisectionLoop.preserves
                                (@HPow.hPow Nat Nat Nat
                                  (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                Q Lax109476Proofs.RamBinaryMinimum.prepare →
                              Lax109476Proofs.RamBisectionLoop.preserves
                                  (@HPow.hPow Nat Nat Nat
                                    (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                  Q Lax109476Proofs.RamBinaryMinimum.finish →
                                Lax808846Proofs.Reasoning.Spec
                                  (@HPow.hPow Nat Nat Nat
                                    (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                  (fun (σ : Lax808846Proofs.Imp.Env) =>
                                    And (Q σ)
                                      (And (@Eq Nat (σ.vars "minimum.bound") D)
                                        (@Eq Nat (@List.length Nat (σ.arrs "cf.stack")) N)))
                                  (Lax109476Proofs.RamBinaryMinimum.minimum queryCom)
                                  (fun (x τ : Lax808846Proofs.Imp.Env) =>
                                    And (Q τ)
                                      (Lax109476Proofs.RamReconstructionRecord.Output
                                        (Lax109476Proofs.BinaryOptimization.minimum query D) τ))
                                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                (@OfNat.ofNat Nat (nat_lit 144) (instOfNatNat (nat_lit 144))) M.size)
                                              (@OfNat.ofNat Nat (nat_lit 342) (instOfNatNat (nat_lit 342))))
                                            queryCost)
                                          (Lax109476Proofs.BinaryOptimization.steps D))
                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                          (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) D.size))
                                      (Lax109476Proofs.RamRationalReconstruction.instructionBound S))
                                    (@OfNat.ofNat Nat (nat_lit 48) (instOfNatNat (nat_lit 48)))) := by sorry
