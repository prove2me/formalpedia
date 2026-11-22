-- Prove2me | Theorems.Thm_MasulloGRH_elemSchwartz_compactSubgroupAverage
-- name    : MasulloGRH.elemSchwartz_compactSubgroupAverage
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T17:15:35.593819+00:00
-- url     : https://prove2.me/theorems/b0a628bb-8e1b-4bbc-b9fe-2375ce2873d4
-- title:
--   Averaging over a compact subgroup is a continuous operator on the elementary Schwartz–Bruhat space
-- statement:
--   Let $E=\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ with $F=\prod_{i<s}\mathbb Z/d_i$ finite ($d_i\neq0$), and let $C\le E$ be a subgroup, with normalized Haar measure $dc$ when $C$ is compact (and the zero measure otherwise, as in the platform's `subgroupHaar`). Then the averaging operator
--   $$(A_Cg)(e)=\int_C g(e+c)\,dc$$
--   maps the Schwartz–Bruhat space $\mathcal S(E)$ (Definition D.1.3.1) into itself and is continuous and linear.
--
--   Proof sketch. A compact subgroup lies in $\{0\}\times\mathbb T^n\times\{0\}\times F$, because nonzero elements of $\mathbb R^m$ or $\mathbb Z^r$ have unbounded multiples. Split $C$ according to the finitely many values $f$ of the $F$-coordinate, and lift the torus coordinate measurably to $[0,1)^n$. This writes $A_C=\sum_f A_{\nu_f}\circ\tau_f$, where $\tau_f$ is translation by $f$ and $A_{\nu_f}$ is the torus average for the push-forward measure $\nu_f$. Both kinds of operator are continuous on $\mathcal S(E)$. This is the first step of Lemma D.1.5.4: averaging over a compact subgroup preserves Schwartz–Bruhat functions.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Definition D.1.3.1 and Lemma D.1.5.4

import Definitions.Def_MasulloGRH_SchwartzBruhatAveraging

set_option autoImplicit false

namespace MasulloGRH

open MeasureTheory

theorem elemSchwartz_compactSubgroupAverage {m n r s : ℕ} {d : Fin s → ℕ} (hd : ∀ i, d i ≠ 0)
    (C : Subgroup (Multiplicative (ElemGroup m n r s d))) :
    ∃ A : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m n r s d, Continuous A ∧
      ∀ (g : ElemSchwartz m n r s d) (e : ElemGroup m n r s d),
        (A g).toFun e = (letI : MeasurableSpace C := borel C
          ∫ c : C, g.toFun (e + Multiplicative.toAdd (c : Multiplicative (ElemGroup m n r s d)))
            ∂ subgroupHaar C) := by
  sorry

end MasulloGRH
