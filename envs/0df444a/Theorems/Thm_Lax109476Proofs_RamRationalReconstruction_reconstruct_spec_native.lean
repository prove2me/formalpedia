-- Prove2me | Theorems.Thm_Lax109476Proofs_RamRationalReconstruction_reconstruct_spec_native
-- name    : Lax109476Proofs.RamRationalReconstruction.reconstruct_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:02:09.545087+00:00
-- url     : https://prove2.me/theorems/0510aab9-d9c5-4fb3-acda-de5821bddda8
-- title:
--   Execute bounded rational interval reconstruction
-- statement:
--   Let $\ell,u$ be rational endpoints with $u\ge0$, each of height at most $2^S$, and let $D$ be a natural denominator bound. Suppose the reconstruction stack has length $N$ covering the source’s depth bound, the host width meets the reconstruction bound and $D<2^w$. The fixed native reconstruction command returns exactly
--   $$\operatorname{out}=\operatorname{reconstruct}(\ell,u,D),$$
--   with the source’s full optional-result encoding and instruction bound $T_{\rm reconstruct}(S)$. This equality covers every endpoint pair satisfying the stated bounds; no promised rational witness is required.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamRationalReconstruction.lean, theorem Lax109476Proofs.RamRationalReconstruction.reconstruct_spec, line 34

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
namespace Lax109476Proofs.RamRationalReconstruction
end Lax109476Proofs.RamRationalReconstruction

theorem Lax109476Proofs.RamRationalReconstruction.reconstruct_spec_native : ∀ (S N w D : Nat) (l u : Rat),
  @LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) u →
    Lax109476Proofs.RationalArithmeticBounds.Height l
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) S) →
      Lax109476Proofs.RationalArithmeticBounds.Height u
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) S) →
        @LE.le Nat instLENat
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (Lax109476Proofs.RamRationalReconstruction.depthBound S)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            N →
          @LE.le Nat instLENat (Lax109476Proofs.RamRationalReconstruction.wordWidth S) w →
            @LT.lt Nat instLTNat D
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w) →
              Lax808846Proofs.Reasoning.Spec
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                (fun (σ : Lax808846Proofs.Imp.Env) =>
                  And (Lax109476Proofs.RamRationalScalars.Value "recon.lo" l σ)
                    (And (Lax109476Proofs.RamRationalScalars.Value "recon.hi" u σ)
                      (And (@Eq Nat (σ.vars "recon.bound") D) (@Eq Nat (@List.length Nat (σ.arrs "cf.stack")) N))))
                Lax109476Proofs.RamRationalReconstruction.reconstruct
                (fun (x τ : Lax808846Proofs.Imp.Env) =>
                  Lax109476Proofs.RamReconstructionRecord.Output
                    (Lax109476Proofs.RationalReconstruction.reconstruct l u D) τ)
                (Lax109476Proofs.RamRationalReconstruction.instructionBound S) := by sorry
