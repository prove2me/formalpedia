-- Prove2me | Theorems.Thm_Lax109476Proofs_RamEllipsoidStep_ellipsoidStep_spec
-- name    : Lax109476Proofs.RamEllipsoidStep.ellipsoidStep_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:31:06.553313+00:00
-- url     : https://prove2.me/theorems/8a3d0f12-dbc0-4d6e-b2e0-fcf6e7e56a5e
-- title:
--   Execution of one rounded ellipsoid step
-- statement:
--   Let $n\ge2$, let $A$ be a rational $n\times n$ matrix, and let $a,c\in\mathbb Q^n$, with $a^TAa>0$. Let $H\ge1$ bound the heights of their entries, and let $M$ bound the intermediate form, dimension and precision quantities. Set $D=2^{2k+3n+9}$ and $E=2^{2n+4}$ at iteration $k$. Under the routine's explicit word-range bounds for modulus $B$, the ellipsoid-step command maps the encoded state $(A,a,c)$ and its allocated workspace to the rounded next center and shape:
--   $$c'=\operatorname{roundedCenter}(n,A,a,c,D),\qquad A'=\operatorname{roundedStepShape}(n,A,a,D,\operatorname{stepAccuracy}(n)).$$
--   It preserves the old shape and center and the dimension field, records the grid $D$, and runs within the explicit bound $K_{\rm step}(n,H,M)$ defined by the implementation. The hypotheses include all rational-height, array-extent and intermediate overflow conditions. This operational interface is reusable both in the feasibility solver and in the native MWIS rounding program.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamEllipsoidStep.lean, theorem ellipsoidStep_spec

import Definitions.Def_EdgeSublinearMWIS_Main_NativeOperationalInterfaces

theorem Lax109476Proofs.RamEllipsoidStep.ellipsoidStep_spec : ∀ (B n H M k : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ),
  2 ≤ n →
    1 ≤ H →
      (∀ (i j : Fin n), Lax109476Proofs.RationalArithmeticBounds.Height (A i j) H) →
        (∀ (i : Fin n), Lax109476Proofs.RationalArithmeticBounds.Height (a i) H) →
          (∀ (i : Fin n), Lax109476Proofs.RationalArithmeticBounds.Height (c i) H) →
            0 < a ⬝ᵥ A.mulVec a →
              n * n ≤ M →
                Lax109476Proofs.RamEllipsoidForm.formHeight n H ≤ M →
                  2 ^ (2 * k + 3 * n + 9) ≤ M →
                    2 ^ (2 * n + 4) ≤ M →
                      2 *
                              Lax109476Proofs.RamShapeCoordinate.shapeCap
                                  (Lax109476Proofs.RamEllipsoidCoefficients.coefficientCap M) ^
                                2 +
                            3 <
                          B →
                        Lax808846Proofs.Reasoning.Spec B
                          (fun (σ : Lax808846Proofs.Imp.Env) =>
                            Lax109476Proofs.RamRationalArrays.Represents "ell.shape"
                                (Lax109476Proofs.RamMatrixStorage.flatten A) σ ∧
                              Lax109476Proofs.RamRationalArrays.Represents "ell.normal" (List.ofFn a) σ ∧
                                Lax109476Proofs.RamRationalArrays.Represents "ell.center" (List.ofFn c) σ ∧
                                  Lax109476Proofs.RamEllipsoidStep.Workspace n σ ∧
                                    σ.vars "vec.n" = n ∧ σ.vars "iter.k" = k)
                          Lax109476Proofs.RamEllipsoidStep.ellipsoidStep
                          (fun (x τ : Lax808846Proofs.Imp.Env) =>
                            Lax109476Proofs.RamRationalArrays.Represents "ell.nextcenter"
                                (List.ofFn
                                  (Lax109476Proofs.EllipsoidCenter.roundedCenter n A a c (2 ^ (2 * k + 3 * n + 9))))
                                τ ∧
                              Lax109476Proofs.RamRationalArrays.Represents "ell.nextshape"
                                  (Lax109476Proofs.RamMatrixStorage.flatten
                                    (Lax109476Proofs.EllipsoidCenter.roundedStepShape n A a (2 ^ (2 * k + 3 * n + 9))
                                      (Lax109476Proofs.EllipsoidIteration.stepAccuracy n)))
                                  τ ∧
                                Lax109476Proofs.RamRationalArrays.Represents "ell.shape"
                                    (Lax109476Proofs.RamMatrixStorage.flatten A) τ ∧
                                  Lax109476Proofs.RamRationalArrays.Represents "ell.center" (List.ofFn c) τ ∧
                                    τ.vars "vec.n" = n ∧ τ.vars "grid.D" = 2 ^ (2 * k + 3 * n + 9))
                          (Lax109476Proofs.RamEllipsoidStep.stepCost n H M) := by sorry
