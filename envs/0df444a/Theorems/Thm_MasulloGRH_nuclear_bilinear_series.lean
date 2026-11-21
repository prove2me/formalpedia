-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_bilinear_series
-- name    : MasulloGRH.nuclear_bilinear_series
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:12:54.938786+00:00
-- url     : https://prove2.me/theorems/e497d87a-7e91-460b-ab05-508eca13655c
-- title:
--   On a nuclear space, a bilinear form bounded by $p(x)r(y)$ is a nuclear series
-- statement:
--   Let $E$ be a nuclear space over $\mathbb C$, $p$ a continuous seminorm on $E$, $F$ a complex vector space (no topology) with a seminorm $r$, and $B\colon E\times F\to\mathbb C$ a bilinear form with
--
--   $$|B(x,y)|\le p(x)\,r(y)\qquad(x\in E,\ y\in F).$$
--
--   Then there are
--
--   1. an equicontinuous sequence $(\varphi_m)_{m\ge0}$ of continuous linear functionals on $E$,
--   2. a sequence $(\psi_m)_{m\ge0}$ of linear functionals on $F$ with $|\psi_m(y)|\le r(y)$ for all $m$ and $y$,
--   3. a sequence $(\lambda_m)_{m\ge0}$ of complex numbers with $\sum_m|\lambda_m|<\infty$,
--
--   such that for all $x\in E$, $y\in F$
--
--   $$B(x,y)=\sum_{m\ge0}\lambda_m\,\varphi_m(x)\,\psi_m(y).$$
--
--   Equivalently: the continuous linear map $E\to(F,r)'$ induced by $B$ into the Banach dual of the seminormed space $(F,r)$ is a nuclear map. This is the core of the Schwartz kernel theorem (Grothendieck: every continuous linear map from a nuclear space into a Banach space is nuclear).
--
--   **Formalization Note** Nuclearity is the predicate `IsNuclear` of the definition file (coincidence of the projective and injective tensor topologies). The series converges absolutely for each fixed $(x,y)$, stated as `HasSum`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Theorem C.2.4.18 (Schwartz kernel theorem) and its proof; cf. Trèves, Topological Vector Spaces, Distributions and Kernels, Ch. 50 (Theorem 50.1 and Proposition 50.5)

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem nuclear_bilinear_series (E F : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] (hE : IsNuclear E)
    (p : Seminorm ℂ E) (hp : Continuous p) (r : Seminorm ℂ F)
    (B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ) (hB : ∀ x y, ‖B x y‖ ≤ p x * r y) :
    ∃ (φ : ℕ → StrongDual ℂ E) (ψ : ℕ → F →ₗ[ℂ] ℂ) (c : ℕ → ℂ),
      Equicontinuous (fun m => (φ m : E → ℂ)) ∧ (∀ m y, ‖ψ m y‖ ≤ r y) ∧
      Summable (fun m => ‖c m‖) ∧
      ∀ x y, HasSum (fun m => c m * φ m x * ψ m y) (B x y) := by sorry

end MasulloGRH
