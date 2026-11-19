-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeSelectedLP_invocation_native
-- name    : Lax263307Proofs.NativeSelectedLP.invocation_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:33:37.450169+00:00
-- url     : https://prove2.me/theorems/effd6f3b-37d9-44fb-abeb-9daf93f1ea2b
-- title:
--   Selected LP invocation under uniform resource bounds
-- statement:
--   Let $G$ be a finite graph, and let a fixed rational LP program provide its stated certificate and execution guarantees. Suppose the graph order, relaxation level, accuracy parameters and moment dimension are bounded by a common root parameter $R$, and every center coordinate has height at most $80(R+1)$. At every word width at least the prescribed root bound, the projection command returns the exact functional projection and preserves its dimension field within
--   $$T\le \operatorname{callCost}(p,R).$$
--   The precondition is the complete encoded invocation state. This interface keeps the same chosen LP program throughout a recursive computation.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeSelectedLP.lean#L79

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
namespace Lax263307Proofs.NativeSelectedLP
end Lax263307Proofs.NativeSelectedLP

theorem Lax263307Proofs.NativeSelectedLP.invocation_native : ∀ {f : List Nat → List Nat} (p : Lax263307Proofs.NativeSelectedLP.Program f) {n : Nat} (G : SimpleGraph (Fin n))
  [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (k r D F R w : Nat)
  (center : Lax263307.MomentLP.Index n r → Rat),
  @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) D →
      @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
        @LE.le Nat instLENat n R →
          @LE.le Nat instLENat k R →
            @LE.le Nat instLENat r R →
              @LE.le Nat instLENat D R →
                @LE.le Nat instLENat F R →
                  @LE.le Nat instLENat (Lax263307.MomentLP.dimension n r) R →
                    (∀ (i : Lax263307.MomentLP.Index n r),
                        Lax263307.NativeRoundedStep.height (center i)
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) R
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                      @LE.le Nat instLENat (@Lax263307Proofs.NativeSelectedLP.wordHeight f p R) w →
                        Lax808846Proofs.Reasoning.Spec
                          (@HPow.hPow Nat Nat Nat
                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                          (@Lax263307Proofs.NativeProjectionTrace.InvocationInput (Lax263307.MomentLP.rowCount n r)
                            (Lax263307.MomentLP.dimension n r) (@Lax263307.MomentLP.program n G inst k r)
                            (@Lax263307.ProjectedOracle.raw (Lax263307.MomentLP.dimension n r) center)
                            (Lax263307Proofs.NativeNodeTolerance.tolerance n D F)
                            (@Lax263307Proofs.NativeSelectedLP.oracleTime f p R))
                          (Lax263307Proofs.NativeProjectionOracle.command
                            (@Lax263307Proofs.NativeSelectedLP.Program.code f p)
                            (@Lax263307Proofs.NativeSelectedLP.Program.coeff f p))
                          (fun (x τ : Lax808846Proofs.Imp.Env) =>
                            And
                              (@Lax263307Proofs.NativeProjectionResult.Output (Lax263307.MomentLP.dimension n r)
                                (@Lax263307Proofs.NativeOracleExecution.projection n r f G inst k D F center) τ)
                              (@Eq Nat (τ.vars "projection.n") (Lax263307.MomentLP.dimension n r)))
                          (@Lax263307Proofs.NativeSelectedLP.callCost f p R) := by sorry
