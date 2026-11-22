-- Prove2me | Theorems.Thm_MasulloGRH_nuclearFrechet_schauderBasis_kotheEchelon
-- name    : MasulloGRH.nuclearFrechet_schauderBasis_kotheEchelon
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:01:44.452875+00:00
-- url     : https://prove2.me/theorems/72abcdc2-ab9b-4778-85f3-c464346a045d
-- title:
--   A nuclear Fréchet space with a Schauder basis is isomorphic, via the coefficient map, to a Köthe echelon space $\lambda^1(A)$
-- statement:
--   **Nuclear Fréchet spaces with a basis are Köthe sequence spaces.** Let $E$ be a complex nuclear Fréchet space and $(x_m)_{m\ge0}$ a Schauder basis of $E$ with coefficient functionals $(f_m)_{m\ge0}\subset E'$. Then there is a Köthe matrix $A=(a_{k,m})_{k,m\in\mathbb N}$ such that the coefficient map
--   $$T:E\longrightarrow\lambda^1(A),\qquad T(u)=\big(f_m(u)\big)_{m\ge0},$$
--   is well defined and is a linear topological isomorphism of $E$ onto the Köthe echelon space
--   $$\lambda^1(A)=\Big\{\xi\in\mathbb C^{\mathbb N}:\ \sum_{m\ge0}a_{k,m}|\xi_m|<\infty\ \text{for all }k\Big\}$$
--   with the topology of the seminorms $\xi\mapsto\sum_m a_{k,m}|\xi_m|$. (One may take $a_{k,m}=p_k(x_m)$ for an increasing fundamental sequence $(p_k)$ of continuous seminorms of $E$.)
--
--   This is the consequence of the Dynin–Mityagin theorem (Theorem 4.1.2.6: every Schauder basis of a nuclear Fréchet space is absolute) recorded in the paper right after that theorem; the Köthe matrix encodes the growth of the basis vectors with respect to the continuous seminorms of $E$, and in the cases of interest to the paper the resulting sequence space is the space $\mathfrak s$ of rapidly decreasing sequences.
--
--   **Formalization Note.** Uses the platform notions `MasulloGRH.IsNuclear`, `MasulloGRH.IsFrechet`, `MasulloGRH.IsSchauderBasis`, and the new definition `SchauderBasis_KotheEchelon` (`IsKotheMatrix`, and `KotheEchelon a` with the topology of the seminorms $p_k$). `T u m` denotes the $m$-th coordinate of `T u`. The paper only says that $E$ is linearly and topologically isomorphic to a Köthe sequence space; the formal statement also records that the isomorphism is the coefficient map, which is the classical form of the result.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 161, §4.1.2.1, paragraph following Theorem 4.1.2.6; classical reference: H. Jarchow, Locally Convex Spaces, Teubner, 1981, Part III, Ch. 21, §21.6, p. 496 (as cited by the paper), together with Theorem 4.1.2.6 (Dynin–Mityagin)

import Definitions.Def_MasulloGRH_SchauderBases
import Definitions.Def_SchauderBasis_KotheEchelon

open Filter Topology

set_option autoImplicit false

namespace MasulloGRH

theorem nuclearFrechet_schauderBasis_kotheEchelon
    (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hN : IsNuclear E) (hF : IsFrechet E) (x : ℕ → E) (f : ℕ → StrongDual ℂ E)
    (hx : IsSchauderBasis x f) :
    ∃ a : ℕ → ℕ → ℝ, SchauderBasis.IsKotheMatrix a ∧
      ∃ T : E ≃L[ℂ] SchauderBasis.KotheEchelon a, ∀ (u : E) (m : ℕ), T u m = f m u := by sorry

end MasulloGRH
