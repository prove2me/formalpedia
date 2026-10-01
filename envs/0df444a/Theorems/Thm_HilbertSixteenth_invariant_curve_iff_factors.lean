-- Prove2me | Theorems.Thm_HilbertSixteenth_invariant_curve_iff_factors
-- name    : HilbertSixteenth.invariant_curve_iff_factors
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:28:40.353991+00:00
-- url     : https://prove2.me/theorems/ee35788e-7f7e-4657-bdfc-2d6a8c0e6092
-- title:
--   Proposition 3: invariant curves and their irreducible factors
-- statement:
--   Let $V=(P,Q)$ be a polynomial vector field and let
--   $$f = c\, f_1^{n_1}\cdots f_r^{n_r}$$
--   be the factorization of $f\in\mathbb R[x,y]$ into irreducible factors, with $c\neq0$ a constant, the $f_i$ irreducible and pairwise non-associated, and $n_i\ge1$. Then $f=0$ is an invariant algebraic curve of $V$ (for some cofactor $K_f$) if and only if each $f_i=0$ is an invariant algebraic curve of $V$ (for some cofactor $K_{f_i}$). Moreover, in that case
--   $$K_f = n_1K_{f_1}+\cdots+n_rK_{f_r}.$$
--
--   This reduces the study of invariant algebraic curves to irreducible ones.
--
--   **Formalization Note** The constant $c$ accounts for the fact that factorizations in $\mathbb R[x,y]$ are unique only up to units. For $r=0$ the polynomial is the constant $c$.
-- source:
--   J. Llibre, *Sobre el problema 16 de Hilbert*, La Gaceta de la RSME 18 (2015), no. 3, pp. 543–554, §7, Proposition 3 (see also J. Llibre, Integrability of polynomial differential systems, Handbook of Differential Equations, 2004).

import Definitions.Def_HilbertSixteenth_PolyFields

namespace HilbertSixteenth
theorem invariant_curve_iff_factors (V : PolyField) (r : ℕ) (c : ℝ) (hc : c ≠ 0)
    (g : Fin r → Poly2) (n : Fin r → ℕ) (hirr : ∀ i, Irreducible (g i))
    (hdist : ∀ i j, i ≠ j → ¬ Associated (g i) (g j)) (hn : ∀ i, 1 ≤ n i) :
    ((∃ K : Poly2, IsInvariantCurve V (MvPolynomial.C c * ∏ i, g i ^ n i) K) ↔
        ∀ i, ∃ K : Poly2, IsInvariantCurve V (g i) K) ∧
      ∀ (K : Poly2) (Ks : Fin r → Poly2),
        IsInvariantCurve V (MvPolynomial.C c * ∏ i, g i ^ n i) K →
        (∀ i, IsInvariantCurve V (g i) (Ks i)) →
        K = ∑ i, (n i : Poly2) * Ks i := by sorry
end HilbertSixteenth
