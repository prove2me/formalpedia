-- Prove2me | Theorems.Thm_Lax109476Proofs_RamEllipsoidCoefficients_computeCoefficients_spec
-- name    : Lax109476Proofs.RamEllipsoidCoefficients.computeCoefficients_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:30:58.963838+00:00
-- url     : https://prove2.me/theorems/0b0312f2-13c2-474b-89a9-73967db2b3ae
-- title:
--   Execution of rational ellipsoid coefficient computation
-- statement:
--   Let $n\ge2$ be the dimension and $q>0$ the rational quadratic-form value. Let $D,E>0$ be the precision grids, $M$ a height and magnitude bound, $C$ a height bound for the resulting five coefficients, and $B$ the machine modulus. Assume the explicit intermediate word-range inequalities and that the scalar input fields and five allocated zero coefficient entries are present. The coefficient command writes exactly the implementation's vector $g(n,q,D,E)$ and preserves its scalar input:
--   $$\operatorname{coefficients}_{\rm out}=g(n,q,D,E),\qquad T\le582\,\operatorname{size}(M)+687.$$
--   Here $\operatorname{size}(M)$ is the binary length of $M$. The vector contains the rational scaling, rank-one, center, inflation and diagonal coefficients for the rounded ellipsoid update. This is a reusable operational specification of their computation, including the necessary arithmetic bounds.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamEllipsoidCoefficients.lean, theorem computeCoefficients_spec

import Definitions.Def_EdgeSublinearMWIS_Main_NativeOperationalInterfaces

theorem Lax109476Proofs.RamEllipsoidCoefficients.computeCoefficients_spec : ∀ (B n M C D E : ℕ) (q : ℚ),
  2 ≤ n →
    0 < q →
      Lax109476Proofs.RationalArithmeticBounds.Height q M →
        n ≤ M →
          D ≤ M →
            E ≤ M →
              0 < D →
                0 < E →
                  n ^ 2 < B →
                    (E + 1) ^ 2 < B →
                      2 * M ^ 2 + 3 < B →
                        (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B →
                          C < B →
                            (∀ v ∈ Lax109476Proofs.RamEllipsoidCoefficients.coefficients n q D E,
                                Lax109476Proofs.RationalArithmeticBounds.Height v C) →
                              Lax808846Proofs.Reasoning.Spec B
                                (fun (σ : Lax808846Proofs.Imp.Env) =>
                                  Lax109476Proofs.RamEllipsoidCoefficients.ScalarInput n q D E σ ∧
                                    Lax109476Proofs.RamRationalArrays.Represents "ell.coeff" (List.replicate 5 0) σ)
                                Lax109476Proofs.RamEllipsoidCoefficients.computeCoefficients
                                (fun (x τ : Lax808846Proofs.Imp.Env) =>
                                  Lax109476Proofs.RamRationalArrays.Represents "ell.coeff"
                                      (Lax109476Proofs.RamEllipsoidCoefficients.coefficients n q D E) τ ∧
                                    Lax109476Proofs.RamEllipsoidCoefficients.ScalarInput n q D E τ)
                                (582 * M.size + 687) := by sorry
