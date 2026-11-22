-- Prove2me | Theorems.Thm_MasulloGRH_elemSchwartz_torusAverage
-- name    : MasulloGRH.elemSchwartz_torusAverage
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T17:08:17.947648+00:00
-- url     : https://prove2.me/theorems/28f9b5c8-6b86-424b-aa63-04f57c5dd452
-- title:
--   Averaging over torus translations is a continuous operator on the elementary Schwartz–Bruhat space
-- statement:
--   Let $E=\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ with $F=\prod_{i<s}\mathbb Z/d_i$, and let $\nu$ be a finite Borel measure on $\mathbb R^n$. For $g\in\mathcal S(E)$ define the torus average
--   $$(A_\nu g)(x,z,a,b)=\int_{\mathbb R^n} g\big(x,\ z+[v],\ a,\ b\big)\,d\nu(v),\qquad [v]=v \bmod \mathbb Z^n .$$
--   Then $A_\nu$ maps the Schwartz–Bruhat space $\mathcal S(E)$ (Definition D.1.3.1) into itself and is a continuous linear operator for its seminorm topology. In fact $D^k(A_\nu g)=\int D^kg(\cdot+(0,v))\,d\nu(v)$ and $\nu_{i,j,k}(A_\nu g)\le \nu(\mathbb R^n)\,\nu_{i,j,k}(g)$, because translation in the torus variable does not change the weights $|a|^j|x|^i$.
--
--   Taking for $\nu$ the push-forward of the normalized Haar measure of a compact subgroup $C\subseteq\mathbb T^n$ along a measurable section $\mathbb T^n\to[0,1)^n$, this shows that averaging over a compact subgroup of the torus factor preserves $\mathcal S(E)$ continuously. That is one step in the proof of Lemma D.1.5.4 (averaging over $k$ maps $\mathcal S(G)$ to itself).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Definition D.1.3.1 and Lemma D.1.5.4

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

namespace MasulloGRH

open MeasureTheory

theorem elemSchwartz_torusAverage {m n r s : ℕ} {d : Fin s → ℕ}
    (ν : Measure (Fin n → ℝ)) [IsFiniteMeasure ν] :
    ∃ A : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m n r s d, Continuous A ∧
      ∀ (g : ElemSchwartz m n r s d) (e : ElemGroup m n r s d),
        (A g).toFun e =
          ∫ v, g.toFun (e.1, e.2.1 + (fun j => ((v j : ℝ) : UnitAddCircle)), e.2.2) ∂ν := by
  sorry

end MasulloGRH
