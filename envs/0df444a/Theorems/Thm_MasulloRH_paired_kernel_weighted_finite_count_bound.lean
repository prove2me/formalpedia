-- Prove2me | Theorems.Thm_MasulloRH_paired_kernel_weighted_finite_count_bound
-- name    : MasulloRH.paired_kernel_weighted_finite_count_bound
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-22T00:45:31.927594+00:00
-- url     : https://prove2.me/theorems/fd262b93-f1e2-48fa-862b-977d829a1de7
-- title:
--   Weighted finite-family count from the paired compensated resolvent kernel
-- statement:
--   Let I be any finite index type. For each i in I, let beta_i lie in [0,1], let gamma_i be real with gamma_i squared at least 36, and let w_i be a nonnegative real weight. Fix any real center T. Define the actual rational real-resolvent kernel
--
--   $$K(\beta,\gamma,T)=\frac{13/8-\beta}{(13/8-\beta)^2+(\gamma-T)^2}-\frac{5/2-\beta}{(5/2-\beta)^2+\gamma^2}+\frac{169}{31}\left(\frac{3-\beta}{(3-\beta)^2+\gamma^2}-\frac{5/2-\beta}{(5/2-\beta)^2+\gamma^2}\right),$$
--
--   and its reflected average $\overline K(\beta,\gamma,T)=[K(\beta,\gamma,T)+K(1-\beta,\gamma,T)]/2$. Then
--
--   $$\frac{9288}{20737}\sum_{i:\,|\gamma_i-T|\le1}w_i\le\sum_{i\in I}w_i\,\overline K(\beta_i,\gamma_i,T).$$
--
--   The window has radius 1 and total width 2. Kernel nonnegativity outside the window and the response lower bound inside it are proved from the literal rational expressions, rather than assumed. The constant 169/31 is justified by the paired compensation inequality; the response 9288/20737 follows from an exact polynomial factorization.
--
--   The conclusion counts the supplied weighted indices. Applying it to zeros requires independently identifying these inputs and weights with the intended divisor and multiplicities, and establishing any reflection/reindexing or arithmetic trace identity needed to evaluate the right side. No such zero identity or global hypothesis is part of this finite real-variable theorem.
-- source:
--   Independent real-variable kernel and finite-sum argument developed in rounds eight and nine for the Prove2Me Masullo RH specialization mission. The proof includes the paired169/31 compensation certificate and the exact local-response factorization, and imports only Mathlib. It is not attributed to a manuscript passage.

import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem MasulloRH.paired_kernel_weighted_finite_count_bound
    {ι : Type*} [Fintype ι] (β γ w : ι → ℝ) (T : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hβ : ∀ i, β i ∈ Set.Icc (0:ℝ) 1)
    (hgap : ∀ i, 36 ≤ (γ i)^2) :
    (9288/20737:ℝ) * (Finset.univ.filter (fun i => |γ i-T| ≤ 1)).sum w ≤
      ∑ i, w i *
        ((((13/8-β i)/((13/8-β i)^2+(γ i-T)^2) -
            (5/2-β i)/((5/2-β i)^2+(γ i)^2) +
            (169/31)*((3-β i)/((3-β i)^2+(γ i)^2)-
              (5/2-β i)/((5/2-β i)^2+(γ i)^2))) +
          ((13/8-(1-β i))/((13/8-(1-β i))^2+(γ i-T)^2) -
            (5/2-(1-β i))/((5/2-(1-β i))^2+(γ i)^2) +
            (169/31)*((3-(1-β i))/((3-(1-β i))^2+(γ i)^2)-
              (5/2-(1-β i))/((5/2-(1-β i))^2+(γ i)^2))))/2) := by sorry
