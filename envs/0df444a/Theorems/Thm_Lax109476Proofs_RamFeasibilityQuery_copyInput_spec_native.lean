-- Prove2me | Theorems.Thm_Lax109476Proofs_RamFeasibilityQuery_copyInput_spec_native
-- name    : Lax109476Proofs.RamFeasibilityQuery.copyInput_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:02:01.457127+00:00
-- url     : https://prove2.me/theorems/f269dceb-8d3a-44bd-ab59-58dbddde7606
-- title:
--   Copy a rational feasibility query into its cleared integer workspace
-- statement:
--   Let $P$ be a rational $m\times n$ linear program and let $L$ be its binary encoding size. Suppose $w$ meets the decoding word bound at $2L$ and the full stored rational query predicate holds. The fixed copying command produces the padded-feasibility input for the denominator-cleared integer system:
--   $$\operatorname{Input}_{\rm integer}(\operatorname{integerProgram}(P),L).$$
--   It runs in at most $71(mn+m)+58$ instructions. This supplies the exact data conversion consumed by rational feasibility execution.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamFeasibilityQuery.lean, theorem Lax109476Proofs.RamFeasibilityQuery.copyInput_spec, line 33

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
namespace Lax109476Proofs.RamFeasibilityQuery
end Lax109476Proofs.RamFeasibilityQuery

theorem Lax109476Proofs.RamFeasibilityQuery.copyInput_spec_native : ∀ (m n : Nat) (P : Lax109476.LinearProgram.Program Rat m n) (w : Nat),
  @LE.le Nat instLENat
      (Lax109476Proofs.RamDecoder.wordWidth
        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (Lax759944.BinaryWordEncoding.bitSize (@Lax109476.RationalEncoding.encodeProgram m n P))))
      w →
    Lax808846Proofs.Reasoning.Spec
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
      (@Lax109476Proofs.RamFeasibilityQuery.Input m n P) Lax109476Proofs.RamFeasibilityQuery.copyInput
      (fun (x τ : Lax808846Proofs.Imp.Env) =>
        @Lax109476Proofs.RamPaddedFeasibility.Input m n (@Lax109476Proofs.IntegerEncoding.integerProgram m n P)
          (Lax759944.BinaryWordEncoding.bitSize (@Lax109476.RationalEncoding.encodeProgram m n P)) τ)
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 71) (instOfNatNat (nat_lit 71)))
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) m n) m))
        (@OfNat.ofNat Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))) := by sorry
