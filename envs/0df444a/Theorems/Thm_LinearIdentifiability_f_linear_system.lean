-- Prove2me | Theorems.Thm_LinearIdentifiability_f_linear_system
-- name    : LinearIdentifiability.f_linear_system
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T07:36:40.542604+00:00
-- url     : https://prove2.me/theorems/66d017b9-7e75-4b1a-9eaa-0f47e5420bba
-- title:
--   Theorem 1, eq. (8): the linear system for $f$ at an input $x$
-- statement:
--   Let $p_{\mathcal D}$ be a data distribution, let $(f',g')$ and $(f^*,g^*)$ be models of the form (1) with $p'=p^*$ on the data, and fix an input $x$. Suppose there are $M$ tuples $(y_A^{(i)},y_B^{(i)})$, $i=1,\dots,M$, such that for each $i$ both $y_A^{(i)}$ and $y_B^{(i)}$ lie in some candidate set $S$ with $p_{\mathcal D}(x,S)>0$, and such that the matrices $L'$ and $L^*$ with columns $g'(y_A^{(i)})-g'(y_B^{(i)})$ and $g^*(y_A^{(i)})-g^*(y_B^{(i)})$ are invertible (the diversity condition at $x$). Then
--
--   $$L'^\top f'(x)=L^{*\top}f^*(x),\qquad f'(x)=(L^*L'^{-1})^\top f^*(x),$$
--
--   and $(L^*L'^{-1})^\top$ is invertible.
--
--   **Formalization Note** The paper says the tuples are distinct; this follows from the invertibility of $L'$ and is not stated separately. The text after eq. (8) writes $A=L^*L'^{-1}$ while eq. (8) has the transpose; the statement follows eq. (8).
-- source:
--   Roeder, Metz and Kingma, On Linear Identifiability of Learned Representations, arXiv:2007.00810v3 (2020), Section 3.2, diversity condition and proof of Theorem 1, eq. (8), pp. 4-5

import Mathlib
import Definitions.Def_LinearIdentifiability_Basic

open Matrix

namespace LinearIdentifiability

theorem f_linear_system {X Y : Type*} {M : ℕ}
    (pD : PMF (X × Y × Finset Y)) (hD : IsDataDistribution pD)
    (f' fstar : X → Fin M → ℝ) (g' gstar : Y → Fin M → ℝ)
    (hp : ModelsAgreeOnData pD f' g' fstar gstar)
    (x : X) (a b : Fin M → Y)
    (hab : ∀ i, ∃ S, IsSupported pD x S ∧ a i ∈ S ∧ b i ∈ S)
    (hL' : IsUnit (diffMatrix g' a b).det) (hLstar : IsUnit (diffMatrix gstar a b).det) :
    (diffMatrix g' a b)ᵀ *ᵥ f' x = (diffMatrix gstar a b)ᵀ *ᵥ fstar x ∧
      f' x = (diffMatrix gstar a b * (diffMatrix g' a b)⁻¹)ᵀ *ᵥ fstar x ∧
      IsUnit (diffMatrix gstar a b * (diffMatrix g' a b)⁻¹)ᵀ.det := by sorry

end LinearIdentifiability
