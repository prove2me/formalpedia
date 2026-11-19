-- Prove2me | Theorems.Thm_Lax109476Proofs_RamShapeUpdate_updateShape_ellipsoid_spec
-- name    : Lax109476Proofs.RamShapeUpdate.updateShape_ellipsoid_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:30:56.757074+00:00
-- url     : https://prove2.me/theorems/c450a94f-bb6f-4edb-a6d2-728806d6ab0e
-- title:
--   Execution of the rounded ellipsoid shape update
-- statement:
--   Let $A$ be a rational $n\times n$ matrix, $a\in\mathbb Q^n$, $D>0$ a grid and $\eta\in\mathbb Q$ an inflation parameter. Assume the coefficient vector $g$ has at least five entries and satisfies
--   $$g_0=\frac{n^2}{n^2-1},\quad g_1=\frac{2}{(n+1)a^TAa},\quad g_3=(1+\eta)^2,\quad g_4=\frac nD.$$
--   Let $M\ge1$ bound the heights of $A$, $Aa$ and these coefficients, with $n^2,D\le M$ and the routine's explicit word-range bounds for modulus $B$. Given their encodings and three next-shape arrays of length $n^2$, the command writes $\operatorname{roundedStepShape}(n,A,a,D,\eta)$ in flattened order. It preserves $Aa,A,g,n,D$ and runs in at most $(468\operatorname{size}(\operatorname{shapeCap}(M))+731)n^2+36$ steps. This links the matrix-entry loop to the mathematical rounded update.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamShapeUpdate.lean, theorem updateShape_ellipsoid_spec

import Definitions.Def_EdgeSublinearMWIS_Main_NativeOperationalInterfaces

theorem Lax109476Proofs.RamShapeUpdate.updateShape_ellipsoid_spec : ∀ (B n M D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℚ) (gs : List ℚ) (hg : 4 < gs.length) (η : ℚ),
  1 ≤ M →
    n * n ≤ M →
      (∀ (j : Fin n), Lax109476Proofs.RationalArithmeticBounds.Height (A.mulVec a j) M) →
        (∀ (i j : Fin n), Lax109476Proofs.RationalArithmeticBounds.Height (A i j) M) →
          Lax109476Proofs.RationalArithmeticBounds.Height gs[0] M →
            Lax109476Proofs.RationalArithmeticBounds.Height gs[1] M →
              Lax109476Proofs.RationalArithmeticBounds.Height gs[3] M →
                Lax109476Proofs.RationalArithmeticBounds.Height gs[4] M →
                  D ≤ M →
                    0 < D →
                      n * n < B →
                        n < B →
                          2 * Lax109476Proofs.RamShapeCoordinate.shapeCap M ^ 2 + 3 < B →
                            gs[0] = ↑n ^ 2 / (↑n ^ 2 - 1) →
                              gs[1] = 2 / ((↑n + 1) * a ⬝ᵥ A.mulVec a) →
                                gs[3] = (1 + η) ^ 2 →
                                  gs[4] = ↑n / ↑D →
                                    Lax808846Proofs.Reasoning.Spec B
                                      (fun (σ : Lax808846Proofs.Imp.Env) =>
                                        Lax109476Proofs.RamRationalArrays.Represents "ell.u" (List.ofFn (A.mulVec a))
                                            σ ∧
                                          Lax109476Proofs.RamRationalArrays.Represents "ell.shape"
                                              (Lax109476Proofs.RamMatrixStorage.flatten A) σ ∧
                                            Lax109476Proofs.RamRationalArrays.Represents "ell.coeff" gs σ ∧
                                              (σ.arrs "ell.nextshape.s").length = n * n ∧
                                                (σ.arrs "ell.nextshape.n").length = n * n ∧
                                                  (σ.arrs "ell.nextshape.d").length = n * n ∧
                                                    σ.vars "vec.n" = n ∧ σ.vars "grid.D" = D)
                                      Lax109476Proofs.RamShapeUpdate.updateShape
                                      (fun (x τ : Lax808846Proofs.Imp.Env) =>
                                        Lax109476Proofs.RamRationalArrays.Represents "ell.nextshape"
                                            (Lax109476Proofs.RamMatrixStorage.flatten
                                              (Lax109476Proofs.EllipsoidCenter.roundedStepShape n A a D η))
                                            τ ∧
                                          Lax109476Proofs.RamRationalArrays.Represents "ell.u" (List.ofFn (A.mulVec a))
                                              τ ∧
                                            Lax109476Proofs.RamRationalArrays.Represents "ell.shape"
                                                (Lax109476Proofs.RamMatrixStorage.flatten A) τ ∧
                                              Lax109476Proofs.RamRationalArrays.Represents "ell.coeff" gs τ ∧
                                                τ.vars "vec.n" = n ∧ τ.vars "grid.D" = D)
                                      (33 * (n * n) + 26 +
                                        ((468 * (Lax109476Proofs.RamShapeCoordinate.shapeCap M).size + 690 + 4 + 4) *
                                            (n * n) +
                                          10)) := by sorry
