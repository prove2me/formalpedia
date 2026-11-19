-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeRootBudget_command_spec_native
-- name    : Lax263307Proofs.NativeRootBudget.command_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:01:10.570277+00:00
-- url     : https://prove2.me/theorems/a1c217fa-a088-456f-b8b6-a4470b2802f1
-- title:
--   Compute the native root envelope and workspace budget
-- statement:
--   Let $C,d,Q,e,n,D$ be natural numbers, with $n,D>0$. Write $L=\operatorname{logarithm}(n)$, $X=DL$, $H=CX^d$, $R=2^H$ and $W=Q(R+1)^e$. Suppose the complete arithmetic guard
--   $$C+d+Q+e+2n+D+L+X+X^d+H+R+(R+1)^e+W+2(W+1)+100<B.$$
--   From stored $n,D$, one fixed command computes resource $R$, rounding width $W$ and recursion stride $2(W+1)$ while preserving $n,D$. Its instruction bound is
--   $$12\operatorname{size}(n)+12\operatorname{size}(2n)+12d+12H+12e+78.$$
--   Thus these resource quantities are calculated by the program itself.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeRootBudget.lean, theorem Lax263307Proofs.NativeRootBudget.command_spec, line 70

import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
namespace Lax263307Proofs.NativeRootBudget
end Lax263307Proofs.NativeRootBudget

theorem Lax263307Proofs.NativeRootBudget.command_spec_native : ∀ (B C d Q e n D : Nat),
  @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) D →
      @LT.lt Nat instLTNat (Lax263307Proofs.NativeRootBudget.guard C d Q e n D) B →
        Lax808846Proofs.Reasoning.Spec B
          (fun (σ : Lax808846Proofs.Imp.Env) => And (@Eq Nat (σ.vars "graph.n") n) (@Eq Nat (σ.vars "node.D") D))
          (Lax263307Proofs.NativeRootBudget.command C d Q e)
          (fun (x τ : Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (τ.vars "graph.n") n)
              (And (@Eq Nat (τ.vars "node.D") D)
                (And (@Eq Nat (τ.vars "algorithm.resource") (Lax263307Proofs.NativeRootResource.envelope C d n D))
                  (And (@Eq Nat (τ.vars "algorithm.roundWidth") (Lax263307Proofs.NativeRootResource.budget Q e C d n D))
                    (@Eq Nat (τ.vars "recursion.stride")
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (Lax263307Proofs.NativeRootResource.budget Q e C d n D)
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) n.size)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n).size))
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) d))
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                  (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) C
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) D (Lax263307.AlgorithmParameters.logarithm n))
                      d))))
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
            (@OfNat.ofNat Nat (nat_lit 78) (instOfNatNat (nat_lit 78)))) := by sorry
