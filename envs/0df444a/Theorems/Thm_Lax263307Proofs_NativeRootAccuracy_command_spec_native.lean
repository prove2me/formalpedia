-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeRootAccuracy_command_spec_native
-- name    : Lax263307Proofs.NativeRootAccuracy.command_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:01:11.201199+00:00
-- url     : https://prove2.me/theorems/7f95f83b-9aff-4e24-b7b5-739d1755f31a
-- title:
--   Compute native root accuracy and recursion depth
-- statement:
--   Let $n,M,B$ be natural numbers and let $\varepsilon>0$ be rational with numerator magnitude and denominator at most $M$. Assume
--   $$3M+8(\operatorname{depth}(n)+1)M+2n+\operatorname{depth}(n)+40<B.$$
--   From the stored graph order and rational accuracy, the fixed command preserves the order and computes
--   $$E=\lceil(\varepsilon/2)^{-1}\rceil,\qquad D=4(\operatorname{depth}(n)+1)E,\qquad f=\operatorname{depth}(n)$$
--   in at most $14\operatorname{depth}(n)+28$ instructions. These are the actual root accuracy denominator and recursion fuel used by the program.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeRootAccuracy.lean, theorem Lax263307Proofs.NativeRootAccuracy.command_spec, line 83

import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
namespace Lax263307Proofs.NativeRootAccuracy
end Lax263307Proofs.NativeRootAccuracy

theorem Lax263307Proofs.NativeRootAccuracy.command_spec_native : ∀ (B M n : Nat) (ε : Rat),
  @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε →
    Lax263307Proofs.NativeSignedArithmetic.Bounded M ε →
      @LT.lt Nat instLTNat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) M)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (Lax263307.RecursionDepth.depth n)
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    M))
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
              (Lax263307.RecursionDepth.depth n))
            (@OfNat.ofNat Nat (nat_lit 40) (instOfNatNat (nat_lit 40))))
          B →
        Lax808846Proofs.Reasoning.Spec B
          (fun (σ : Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (σ.vars "graph.n") n)
              (And (@Eq Nat (σ.vars "accuracy.n") ε.num.natAbs) (@Eq Nat (σ.vars "accuracy.d") ε.den)))
          Lax263307Proofs.NativeRootAccuracy.command
          (fun (x τ : Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (τ.vars "graph.n") n)
              (And
                (@Eq Nat (τ.vars "algorithm.E")
                  (@Nat.ceil Rat Rat.semiring Rat.instPartialOrder
                    (@FloorRing.toFloorSemiring Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder
                      Rat.instFloorRing)
                    (@Inv.inv Rat Rat.instInv
                      (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) ε
                        (@OfNat.ofNat Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))))))
                (And
                  (@Eq Nat (τ.vars "node.D")
                    (Lax263307.RecursiveAlgorithm.accuracyDenominator n
                      (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) ε
                        (@OfNat.ofNat Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))))))
                  (@Eq Nat (τ.vars "recursion.fuel") (Lax263307.RecursionDepth.depth n)))))
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
              (@OfNat.ofNat Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) (Lax263307.RecursionDepth.depth n))
            (@OfNat.ofNat Nat (nat_lit 28) (instOfNatNat (nat_lit 28)))) := by sorry
