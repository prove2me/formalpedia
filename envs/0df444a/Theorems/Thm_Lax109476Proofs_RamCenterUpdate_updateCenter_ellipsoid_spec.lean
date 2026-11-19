-- Prove2me | Theorems.Thm_Lax109476Proofs_RamCenterUpdate_updateCenter_ellipsoid_spec
-- name    : Lax109476Proofs.RamCenterUpdate.updateCenter_ellipsoid_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:30:57.826433+00:00
-- url     : https://prove2.me/theorems/c8309efa-4367-4719-90b2-a0ae8b465e12
-- title:
--   Execution of the rounded ellipsoid center update
-- statement:
--   Let $A$ be a rational $n\times n$ matrix, let $a,c\in\mathbb Q^n$, and let $D>0$ be the rounding grid. Let $g$ be the coefficient vector, with its center coefficient equal to $1/((n+1)\operatorname{sqrtUpper}(a^TAa,D))$. Let $M\ge1$ bound the heights of $Aa$, $c$ and this coefficient, and assume $D\le M$, $n<B$ and the prescribed center-overflow bound for modulus $B$. Given encoded $Aa,c,g$ and three next-center arrays of length $n$, the center command produces
--   $$c'=\operatorname{roundedCenter}(n,A,a,c,D).$$
--   It preserves $Aa,c,g,n,D$ and runs in at most $(180\operatorname{size}(\operatorname{centerCap}(M))+359)n+24$ steps. The coefficient vector has at least three entries. The result connects a coordinate loop to the mathematical rounded-center update.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamCenterUpdate.lean, theorem updateCenter_ellipsoid_spec

import Definitions.Def_EdgeSublinearMWIS_Main_NativeOperationalInterfaces

theorem Lax109476Proofs.RamCenterUpdate.updateCenter_ellipsoid_spec : ∀ (B n M D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (gs : List ℚ) (hg : 2 < gs.length),
  1 ≤ M →
    (∀ (j : Fin n), Lax109476Proofs.RationalArithmeticBounds.Height (A.mulVec a j) M) →
      (∀ (j : Fin n), Lax109476Proofs.RationalArithmeticBounds.Height (c j) M) →
        Lax109476Proofs.RationalArithmeticBounds.Height gs[2] M →
          gs[2] = 1 / ((↑n + 1) * Lax109476Proofs.RationalRounding.sqrtUpper (a ⬝ᵥ A.mulVec a) D) →
            D ≤ M →
              0 < D →
                n < B →
                  2 * Lax109476Proofs.RamCenterCoordinate.centerCap M ^ 2 + 3 < B →
                    Lax808846Proofs.Reasoning.Spec B
                      (fun (σ : Lax808846Proofs.Imp.Env) =>
                        Lax109476Proofs.RamRationalArrays.Represents "ell.u" (List.ofFn (A.mulVec a)) σ ∧
                          Lax109476Proofs.RamRationalArrays.Represents "ell.center" (List.ofFn c) σ ∧
                            Lax109476Proofs.RamRationalArrays.Represents "ell.coeff" gs σ ∧
                              (σ.arrs "ell.nextcenter.s").length = n ∧
                                (σ.arrs "ell.nextcenter.n").length = n ∧
                                  (σ.arrs "ell.nextcenter.d").length = n ∧ σ.vars "vec.n" = n ∧ σ.vars "grid.D" = D)
                      Lax109476Proofs.RamCenterUpdate.updateCenter
                      (fun (x τ : Lax808846Proofs.Imp.Env) =>
                        Lax109476Proofs.RamRationalArrays.Represents "ell.nextcenter"
                            (List.ofFn (Lax109476Proofs.EllipsoidCenter.roundedCenter n A a c D)) τ ∧
                          Lax109476Proofs.RamRationalArrays.Represents "ell.u" (List.ofFn (A.mulVec a)) τ ∧
                            Lax109476Proofs.RamRationalArrays.Represents "ell.center" (List.ofFn c) τ ∧
                              Lax109476Proofs.RamRationalArrays.Represents "ell.coeff" gs τ ∧
                                τ.vars "vec.n" = n ∧ τ.vars "grid.D" = D)
                      (33 * n + 18 +
                        ((180 * (Lax109476Proofs.RamCenterCoordinate.centerCap M).size + 318 + 4 + 4) * n + 6)) := by sorry
