-- Prove2me | Theorems.Thm_HodgeComputer_ReflectionChart_certificate_of_relative_primitive
-- name    : HodgeComputer.ReflectionChart.certificate_of_relative_primitive
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T04:57:34.410673+00:00
-- url     : https://prove2.me/theorems/62cd9479-5060-4477-af7f-35c19b081f1d
-- title:
--   Reflection-chart transport from a weighted cubic relative primitive to a projective Hodge certificate
-- statement:
--   Let $F, A \in \mathbb{C}[X_0, X_1, X_2, Y_0, Y_1, Y_2]$ be homogeneous polynomials of degree $6$ with $F$ irreducible, and suppose that along the affine reflection chart
--
--   $$
--   (X_0, X_1, X_2, Y_0, Y_1, Y_2) = (1 + v,\; 1 - v,\; b,\; c + \lambda v,\; c - \lambda v,\; d)
--   $$
--
--   their pullbacks factor through $u = v^2$ as $F|_{\mathrm{chart}} = f(\lambda, b, c, d, v^2)$ and $A|_{\mathrm{chart}} = P(\lambda, b, c, d, v^2)$ for polynomials $f, P \in \mathbb{C}[\lambda, b, c, d, u]$. Assume that $f(\lambda, b, c, d, v^2)$ is irreducible and vanishes at the test point $(0, 0, 0, 0, i)$ with $(\partial_u f)(0, 0, 0, 0, -1) \neq 0$.
--
--   If $(f, P)$ admits a cleared relative two-form primitive on the weighted threefold $f = 0$ — that is, polynomials $D \neq 0$ coprime to $f$, $C_0, C_1, C_2$, and $Q$ satisfying
--
--   $$
--   f_u^2 \sum_{j \in \{b,c,d\}} \Bigl[ f_u (D \partial_j C_j - C_j \partial_j D) - f_j (D \partial_u C_j - C_j \partial_u D) \Bigr] - 2 D^2 (f_u P_u - f_{uu} P) = f Q
--   $$
--
--   — then the projective sextic target $(F, A, q = 1)$ satisfies `HodgeComputer.HasCertificate F A 6 1`.
--
--   This reusable transport theorem eliminates all six-variable Jacobian and homogeneization overhead for any $(01)$-reflection-invariant sextic fourfold, reducing certificate construction on $\mathbb{P}^5$ to a three-component relative primitive on the affine cubic threefold $f(\lambda, b, c, d, u) = 0$.
--
--   **Formalization Note** Coprimality on the double cover $u = v^2$ is deduced via even-exponent monomial projection, and homogeneous clearing into $\mathbb{C}[X_0, \dots, Y_2]$ is carried out via Piola divergence transport on the ambient rational function field.
-- source:
--   Hodge.computer Sextic Fourfold Atlas, Chapter 3B and Discussion #117 (`fqlx`, `benediamond`, `kmehltretter82`), https://hodge.computer/#book/03b-weighted-threefolds and https://github.com/hodge-computer/sextics/discussions/117

import Definitions.Def_HodgeComputerReflectionChart
import Mathlib.RingTheory.Polynomial.UniqueFactorization

theorem HodgeComputer.ReflectionChart.certificate_of_relative_primitive
    (F A : HodgeComputer.AmbientPoly 5) (f P : HodgeComputer.ReflectionChart.ChartPoly)
    (hF_hom : F.IsHomogeneous 6) (hA_hom : A.IsHomogeneous 6)
    (hF_irred : Irreducible F) (hH_irred : Irreducible (HodgeComputer.ReflectionChart.squareLift f))
    (hF_pull : HodgeComputer.ReflectionChart.affinePullback F = HodgeComputer.ReflectionChart.squareLift f)
    (hA_pull : HodgeComputer.ReflectionChart.affinePullback A = HodgeComputer.ReflectionChart.squareLift P)
    (h_pt_zero : MvPolynomial.eval HodgeComputer.ReflectionChart.normalPoint
      (HodgeComputer.ReflectionChart.squareLift f) = 0)
    (h_pt_fu : MvPolynomial.eval HodgeComputer.ReflectionChart.normalPoint
      (HodgeComputer.ReflectionChart.squareLift (MvPolynomial.pderiv 4 f)) ≠ 0)
    (h_prim : HodgeComputer.ReflectionChart.RelativePrimitive f P) :
    HodgeComputer.HasCertificate F A 6 1 := by sorry
