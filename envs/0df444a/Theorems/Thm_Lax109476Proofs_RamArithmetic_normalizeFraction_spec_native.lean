-- Prove2me | Theorems.Thm_Lax109476Proofs_RamArithmetic_normalizeFraction_spec_native
-- name    : Lax109476Proofs.RamArithmetic.normalizeFraction_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:21.501499+00:00
-- url     : https://prove2.me/theorems/b88edcb0-5558-499b-9ed7-a5188b0edf81
-- title:
--   Bounded execution of fraction normalization
-- statement:
--   Let $B,n,d$ be natural numbers with $n<B$, $0<d<B$. Starting with numerator $n$ and denominator $d$ in the rational registers, the normalization command divides both by $g=\gcd(n,d)$. It terminates in at most $36\operatorname{size}(d)+16$ instructions and leaves
--
--   $$n_{\rm out}=n/g,\qquad d_{\rm out}=d/g.$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamArithmetic.lean, theorem normalizeFraction_spec (lines 133–144)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax109476Proofs.RamArithmetic
end Lax109476Proofs.RamArithmetic

theorem Lax109476Proofs.RamArithmetic.normalizeFraction_spec_native : ∀ (B n d : Nat),
  @LT.lt Nat instLTNat n B →
    @LT.lt Nat instLTNat d B →
      @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d →
        Lax808846Proofs.Reasoning.Spec B
          (fun (σ : Lax808846Proofs.Imp.Env) => And (@Eq Nat (σ.vars "rat.n") n) (@Eq Nat (σ.vars "rat.d") d))
          Lax109476Proofs.RamArithmetic.normalizeFraction
          (fun (x σ' : Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (σ'.vars "rat.n") (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) n (n.gcd d)))
              (@Eq Nat (σ'.vars "rat.d") (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) d (n.gcd d))))
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
              (@OfNat.ofNat Nat (nat_lit 36) (instOfNatNat (nat_lit 36))) d.size)
            (@OfNat.ofNat Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))) := by sorry
