-- Prove2me | Theorems.Thm_LinearIdentifiability_g_tilde_linear_system
-- name    : LinearIdentifiability.g_tilde_linear_system
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T07:37:43.321653+00:00
-- url     : https://prove2.me/theorems/2a21ba56-aa57-450f-8e02-a3cc06807fbd
-- title:
--   Appendix C.2, eqs. (16)-(18): the linear system for the augmented $\tilde g$ at a target $y$
-- statement:
--   Let $p_{\mathcal D}$ be a data distribution, let $(f',g')$ and $(f^*,g^*)$ be models of the form (1) with $p'=p^*$ on the data, and fix a target $y$. Suppose there are $M+1$ tuples $(x^{(i)},S^{(i)})$, $i=0,\dots,M$, with $p_{\mathcal D}(x^{(i)},y,S^{(i)})>0$, such that the $(M+1)\times(M+1)$ matrices $\mathbf M'$ and $\mathbf M^*$ with columns $\tilde f'(x^{(i)},S^{(i)})$ and $\tilde f^*(x^{(i)},S^{(i)})$ are invertible (the diversity condition of Appendix C.1 at $y$). Then
--
--   1. $\tilde f'(x^{(i)},S^{(i)})^\top\tilde g'(y)=\tilde f^*(x^{(i)},S^{(i)})^\top\tilde g^*(y)$ for every $i$ (eq. 16);
--   2. $\mathbf M'^\top\tilde g'(y)=\mathbf M^{*\top}\tilde g^*(y)$ (eq. 17);
--   3. $\tilde g'(y)=A\tilde g^*(y)$ with $A=(\mathbf M^*\mathbf M'^{-1})^\top$ (eq. 18), and $A$ is invertible.
--
--   **Formalization Note** Only eqs. (14)-(18) are stated. The paper's subsequent step from $A$ to an $M\times M$ matrix $B$ with $g'(y)=Bg^*(y)$ (eqs. 19-23) is not included because it is false; see the mission description.
-- source:
--   Roeder, Metz and Kingma, On Linear Identifiability of Learned Representations, arXiv:2007.00810v3 (2020), Appendix C.1 (diversity condition) and C.2, eqs. (14)-(18), pp. 14-15

import Mathlib
import Definitions.Def_LinearIdentifiability_Basic

open Matrix

namespace LinearIdentifiability

theorem g_tilde_linear_system {X Y : Type*} {M : ℕ}
    (pD : PMF (X × Y × Finset Y)) (hD : IsDataDistribution pD)
    (f' fstar : X → Fin M → ℝ) (g' gstar : Y → Fin M → ℝ)
    (hp : ModelsAgreeOnData pD f' g' fstar gstar)
    (y : Y) (xs : Fin (M + 1) → X) (Ss : Fin (M + 1) → Finset Y)
    (hpos : ∀ i, pD (xs i, y, Ss i) ≠ 0)
    (hM' : IsUnit (augFMatrix f' g' xs Ss).det) (hMstar : IsUnit (augFMatrix fstar gstar xs Ss).det) :
    (∀ i, augF f' g' (xs i) (Ss i) ⬝ᵥ augG g' y = augF fstar gstar (xs i) (Ss i) ⬝ᵥ augG gstar y) ∧
      (augFMatrix f' g' xs Ss)ᵀ *ᵥ augG g' y = (augFMatrix fstar gstar xs Ss)ᵀ *ᵥ augG gstar y ∧
      augG g' y = (augFMatrix fstar gstar xs Ss * (augFMatrix f' g' xs Ss)⁻¹)ᵀ *ᵥ augG gstar y ∧
      IsUnit (augFMatrix fstar gstar xs Ss * (augFMatrix f' g' xs Ss)⁻¹)ᵀ.det := by sorry

end LinearIdentifiability
