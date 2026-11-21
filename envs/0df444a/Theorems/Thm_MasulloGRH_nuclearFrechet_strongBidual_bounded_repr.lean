-- Prove2me | Theorems.Thm_MasulloGRH_nuclearFrechet_strongBidual_bounded_repr
-- name    : MasulloGRH.nuclearFrechet_strongBidual_bounded_repr
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:30:35.586459+00:00
-- url     : https://prove2.me/theorems/50be0b68-d0e6-4278-8467-1e159a61668e
-- title:
--   Functionals on the strong dual of a nuclear Fréchet space are evaluations at bounded points
-- statement:
--   Let $E$ be a nuclear Fréchet space over $\mathbb C$ and let $q$ be a continuous seminorm on the strong dual $E'_\beta$. Then there is a bounded set $D\subseteq E$ such that every continuous linear functional $F$ on $E'_\beta$ with $|F(f)|\le q(f)$ for all $f$ is the evaluation at some point of $D$: there is $y\in D$ with $F(f)=f(y)$ for every $f\in E'$.
--
--   This combines two classical facts. First, the strong topology has a base of $0$-neighbourhoods given by polars of bounded sets, so $q\le C\,p_{B_0}$ for some bounded $B_0\subseteq E$ and $C\ge0$. Second, a nuclear Fréchet space is Montel, hence (semi-)reflexive, so every $F\in(E'_\beta)'$ is the evaluation at a unique $y\in E$; the bound $|F|\le C\,p_{B_0}$ places $y$ in the bipolar $C\,B_0^{\circ\circ}$, the closed absolutely convex hull of $C B_0$, which is bounded. One takes $D=C\,B_0^{\circ\circ}$.
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Appendix C, §C.1.4 and §C.2.4; cf. H. H. Schaefer, Topological Vector Spaces, Ch. IV §5 and III.7, and A. Pietsch, Nuclear Locally Convex Spaces, 4.4

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem nuclearFrechet_strongBidual_bounded_repr (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear E)
    (q : Seminorm ℂ (StrongDual ℂ E)) (hq : Continuous q) :
    ∃ D : Set E, Bornology.IsVonNBounded ℂ D ∧
      ∀ F : StrongDual ℂ (StrongDual ℂ E), (∀ f, ‖F f‖ ≤ q f) →
        ∃ y ∈ D, ∀ f : StrongDual ℂ E, F f = f y := by sorry

end MasulloGRH
