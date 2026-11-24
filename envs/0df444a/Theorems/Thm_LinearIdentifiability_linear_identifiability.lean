-- Prove2me | Theorems.Thm_LinearIdentifiability_linear_identifiability
-- name    : LinearIdentifiability.linear_identifiability
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T07:38:45.013944+00:00
-- url     : https://prove2.me/theorems/447d4e9f-d772-48e1-a25a-771522767390
-- title:
--   Theorem 1 (as proved): linear identifiability of $f$ and affine identifiability of the context map $g$
-- statement:
--   Let $p_{\mathcal D}$ be an empirical data distribution as in Section 2.1, and let $(f',g')$ and $(f^*,g^*)$ be two models of the form (1), $f:X\to\mathbb R^M$, $g:Y\to\mathbb R^M$, with $p'=p^*$ on the data. Assume:
--
--   1. (diversity for $f$) there are $M$ tuples $(y_A^{(i)},y_B^{(i)})$ such that for every input $x$ in the data and every $i$, $y_A^{(i)}$ and $y_B^{(i)}$ lie in some candidate set $S$ with $p_{\mathcal D}(x,S)>0$, and the matrices $L'$, $L^*$ with columns $g'(y_A^{(i)})-g'(y_B^{(i)})$ and $g^*(y_A^{(i)})-g^*(y_B^{(i)})$ are invertible;
--   2. (diversity for $g$) there are $M+1$ pairs $(x^{(i)},S^{(i)})$ occurring in the data such that every target $y$ in the data lies in every $S^{(i)}$, and the matrices $\mathbf M'$, $\mathbf M^*$ with columns $\tilde f'(x^{(i)},S^{(i)})$ and $\tilde f^*(x^{(i)},S^{(i)})$ are invertible.
--
--   Then:
--
--   1. there is an invertible $M\times M$ matrix $A$ with $f'(x)=Af^*(x)$ for every input $x$ in the data;
--   2. there is an invertible $(M+1)\times(M+1)$ matrix $C$ with $\tilde g'(y)=C\tilde g^*(y)$ for every target $y$ in the data, where $\tilde g(y)=[1;g(y)]$;
--   3. there are an invertible $M\times M$ matrix $B$ and a vector $c\in\mathbb R^M$ with $g'(y)=Bg^*(y)+c$ for every target $y$ in the data.
--
--   Thus the representation $f$ is identifiable up to an invertible linear map, and the context map $g$ up to an invertible affine map.
--
--   **Formalization Note** This is Theorem 1 as its proof establishes it, not as printed. (a) The printed conclusion $g'=Bg^*$ is false: $g'=g^*+c$, $f'=f^*$ gives $p'=p^*$ for every constant vector $c$, and the paper's own diversity conditions can hold in that example; the proof's step from $A$ to $B$ drops the first column of the row-reduction matrix. The proof does establish $\tilde g'=A\tilde g^*$, which is stated as conclusion 2. Conclusion 2 alone does not give an invertible $M\times M$ block, so conclusion 3 is stated separately: it follows from eq. (7) at the inputs $x^{(i)}$ together with conclusion 1, since the vectors $f^*(x^{(i)})$ span $\mathbb R^M$ when $\mathbf M^*$ is invertible. The shift $c$ cannot be removed. (b) The printed diversity conditions choose the tuples separately for each $x$ (resp. each $y$), and then the matrix $(L^*L'^{-1})^\top$ depends on $x$; with such tuples no single $A$ need exist. The proof treats $L',L^*$ (resp. $\mathbf M',\mathbf M^*$) as fixed matrices, so the tuples are taken uniform over the data, as stated. (c) The equalities are asserted on the inputs and targets that occur in the data, since $p'=p^*$ on the data says nothing about $f,g$ elsewhere.
-- source:
--   Roeder, Metz and Kingma, On Linear Identifiability of Learned Representations, arXiv:2007.00810v3 (2020), Section 3.2, Theorem 1, eq. (4), p. 4; proof on pp. 4-5 and Appendix C, eqs. (9)-(18), pp. 14-15

import Mathlib
import Definitions.Def_LinearIdentifiability_Basic

open Matrix

namespace LinearIdentifiability

theorem linear_identifiability {X Y : Type*} {M : ℕ}
    (pD : PMF (X × Y × Finset Y)) (hD : IsDataDistribution pD)
    (f' fstar : X → Fin M → ℝ) (g' gstar : Y → Fin M → ℝ)
    (hp : ModelsAgreeOnData pD f' g' fstar gstar)
    (a b : Fin M → Y)
    (hab : ∀ x ∈ inputSupport pD, ∀ i, ∃ S, IsSupported pD x S ∧ a i ∈ S ∧ b i ∈ S)
    (hL' : IsUnit (diffMatrix g' a b).det) (hLstar : IsUnit (diffMatrix gstar a b).det)
    (xs : Fin (M + 1) → X) (Ss : Fin (M + 1) → Finset Y)
    (hxs : ∀ i, IsSupported pD (xs i) (Ss i)) (hcov : ∀ y ∈ targetSupport pD, ∀ i, y ∈ Ss i)
    (hM' : IsUnit (augFMatrix f' g' xs Ss).det) (hMstar : IsUnit (augFMatrix fstar gstar xs Ss).det) :
    (∃ A : Matrix (Fin M) (Fin M) ℝ, IsUnit A.det ∧
        ∀ x ∈ inputSupport pD, f' x = A *ᵥ fstar x) ∧
      (∃ C : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ, IsUnit C.det ∧
        ∀ y ∈ targetSupport pD, augG g' y = C *ᵥ augG gstar y) ∧
      (∃ (B : Matrix (Fin M) (Fin M) ℝ) (c : Fin M → ℝ), IsUnit B.det ∧
        ∀ y ∈ targetSupport pD, g' y = B *ᵥ gstar y + c) := by sorry

end LinearIdentifiability
