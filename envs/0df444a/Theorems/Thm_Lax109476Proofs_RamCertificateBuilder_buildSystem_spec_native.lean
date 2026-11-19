-- Prove2me | Theorems.Thm_Lax109476Proofs_RamCertificateBuilder_buildSystem_spec_native
-- name    : Lax109476Proofs.RamCertificateBuilder.buildSystem_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:25.010292+00:00
-- url     : https://prove2.me/theorems/a6d51dd3-212c-430a-ac62-0de596674c70
-- title:
--   Build a stored integer certificate system from bounded selectors
-- statement:
--   Let $P$ be a stored source integer program and $F$ an $r\times s$ target program. Suppose the matrix and right-hand-side selectors have the specified bounded execution contracts, preserve the required context fields and arrays, and return the entries of $F$. Under the source-height, dimension and allocated-buffer guards, the fixed nested-loop builder preserves $P$ and stores the entire system:
--
--   $$\mathrm{system.A}=A_F,\qquad\mathrm{system.b}=b_F.$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamCertificateBuilder.lean, theorem buildSystem_spec (lines 18–54)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax109476Proofs.RamCertificateBuilder
end Lax109476Proofs.RamCertificateBuilder

theorem Lax109476Proofs.RamCertificateBuilder.buildSystem_spec_native : ∀ (B M m n r s matrixCost boundCost : Nat) (P : Lax109476.LinearProgram.Program Int m n)
  (F : Lax109476.LinearProgram.Program Int r s) (matrixSelector boundSelector : Lax808846Proofs.Imp.Com),
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
    @LT.lt Nat instLTNat M B →
      @LT.lt Nat instLTNat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) r s)
                r)
              s)
            (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          B →
        (∀ (i : Fin r) (j : Fin s), @LE.le Nat instLENat (@Lax109476.LinearProgram.Program.A Int r s F i j).natAbs M) →
          (∀ (i : Fin r), @LE.le Nat instLENat (@Lax109476.LinearProgram.Program.b Int r s F i).natAbs M) →
            (∀ (i : Fin r) (j : Fin s),
                Lax808846Proofs.Reasoning.Spec B
                  (fun (σ : Lax808846Proofs.Imp.Env) =>
                    And (@Lax109476Proofs.RamCertificateSource.Data m n P σ)
                      (And (@Eq Nat (σ.vars "query.row") (@Fin.val r i)) (@Eq Nat (σ.vars "query.col") (@Fin.val s j))))
                  matrixSelector
                  (fun (x τ : Lax808846Proofs.Imp.Env) =>
                    And (@Lax109476Proofs.RamCertificateSource.Data m n P τ)
                      (Lax109476Proofs.RamRational.FractionOutput
                        (@Int.cast Rat Rat.instIntCast (@Lax109476.LinearProgram.Program.A Int r s F i j)) τ))
                  matrixCost) →
              (∀ (i : Fin r),
                  Lax808846Proofs.Reasoning.Spec B
                    (fun (σ : Lax808846Proofs.Imp.Env) =>
                      And (@Lax109476Proofs.RamCertificateSource.Data m n P σ)
                        (@Eq Nat (σ.vars "query.row") (@Fin.val r i)))
                    boundSelector
                    (fun (x τ : Lax808846Proofs.Imp.Env) =>
                      And (@Lax109476Proofs.RamCertificateSource.Data m n P τ)
                        (Lax109476Proofs.RamRational.FractionOutput
                          (@Int.cast Rat Rat.instIntCast (@Lax109476.LinearProgram.Program.b Int r s F i)) τ))
                    boundCost) →
                (∀ (a : String),
                    @Membership.mem String (List String) (@List.instMembership String)
                        Lax109476Proofs.RamCertificateContext.fields a →
                      a ∉ matrixSelector.wvars) →
                  (∀ (a : String),
                      @Membership.mem String (List String) (@List.instMembership String)
                          Lax109476Proofs.RamCertificateContext.fields a →
                        a ∉ boundSelector.wvars) →
                    "build.i" ∉ matrixSelector.wvars →
                      "build.count" ∉ matrixSelector.wvars →
                        "build.i" ∉ boundSelector.wvars →
                          "build.count" ∉ boundSelector.wvars →
                            @Eq (List String) matrixSelector.warrs (@List.nil String) →
                              @Eq (List String) boundSelector.warrs (@List.nil String) →
                                Lax808846Proofs.Reasoning.Spec B
                                  (fun (σ : Lax808846Proofs.Imp.Env) =>
                                    And (@Lax109476Proofs.RamCertificateContext.Context m n P r s σ)
                                      (And
                                        (Lax109476Proofs.RamEllipsoidStep.Extents "system.A"
                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) r s) σ)
                                        (Lax109476Proofs.RamEllipsoidStep.Extents "system.b" r σ)))
                                  (Lax109476Proofs.RamCertificateBuilder.buildSystem matrixSelector boundSelector)
                                  (fun (x τ : Lax808846Proofs.Imp.Env) =>
                                    And (@Lax109476Proofs.RamCertificateSource.Data m n P τ)
                                      (@Lax109476Proofs.RamEquationData.Data r s F τ))
                                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) matrixCost
                                          (@OfNat.ofNat Nat (nat_lit 70) (instOfNatNat (nat_lit 70))))
                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) r s))
                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) boundCost
                                          (@OfNat.ofNat Nat (nat_lit 58) (instOfNatNat (nat_lit 58))))
                                        r))
                                    (@OfNat.ofNat Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))) := by sorry
