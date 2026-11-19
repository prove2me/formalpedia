-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeOriginalAccuracy_command_spec_native
-- name    : Lax263307Proofs.NativeOriginalAccuracy.command_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:01:15.473373+00:00
-- url     : https://prove2.me/theorems/cd3b9e64-e94d-4196-9119-986ab3ed4363
-- title:
--   Read the original rational accuracy from native input
-- statement:
--   Let $G$ have $n$ vertices and let $w,\varepsilon$ be rational input data. Suppose $n^2+3n+3<B$ and both $|\operatorname{num}(\varepsilon)|$ and $\operatorname{den}(\varepsilon)$ are below the word bound $B$. With the original order and full input tail stored, the fixed reader terminates in at most $18$ instructions and returns
--   $$a_{\rm num}=|\operatorname{num}(\varepsilon)|,\qquad a_{\rm den}=\operatorname{den}(\varepsilon).$$
--   This supplies the original rational accuracy to the native root-parameter computation.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeOriginalAccuracy.lean, theorem Lax263307Proofs.NativeOriginalAccuracy.command_spec, line 21

import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
namespace Lax263307Proofs.NativeOriginalAccuracy
end Lax263307Proofs.NativeOriginalAccuracy

theorem Lax263307Proofs.NativeOriginalAccuracy.command_spec_native : ∀ {n : Nat} (B : Nat) (G : SimpleGraph (Fin n)) [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)]
  (weights : Fin n → Rat) (ε : Rat),
  @LT.lt Nat instLTNat
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            n))
        (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      B →
    @LT.lt Nat instLTNat ε.num.natAbs B →
      @LT.lt Nat instLTNat ε.den B →
        Lax808846Proofs.Reasoning.Spec B
          (fun (σ : Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (σ.vars "input.n") n)
              (Lax455465Proofs.RamVirtualState.Prefix (@Lax263307Proofs.NativeFrontend.tailInput n G inst weights ε)
                "input.data" σ))
          Lax263307Proofs.NativeOriginalAccuracy.command
          (fun (x τ : Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (τ.vars "accuracy.n") ε.num.natAbs) (@Eq Nat (τ.vars "accuracy.d") ε.den))
          (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) := by sorry
