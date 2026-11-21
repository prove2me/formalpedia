-- Prove2me | Theorems.Thm_MasulloGRH_lattice_sum_uniform_convergence
-- name    : MasulloGRH.lattice_sum_uniform_convergence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:53:45.997168+00:00
-- url     : https://prove2.me/theorems/5c114708-0730-4e15-beae-a891bbf2d98b
-- title:
--   Proposition 2.2.1.3 — uniform convergence of $\sum_{\xi\in\Gamma\setminus K}\|\xi+x\|^{-\sigma}$ for $\sigma>N$
-- statement:
--   Let $E$ be a real normed vector space of finite dimension $N$, $\Gamma\subset E$ a full lattice and $K\subset E$ a compact subset. Consider the series
--   $$\sum_{\xi\in\Gamma,\ \xi\notin K}\|\xi+x\|^{-\sigma}.$$
--
--   1. For every real $\sigma>N$ the series converges uniformly for $x\in K$.
--   2. For every $\varepsilon>0$ the series converges uniformly for $(\sigma,x)\in[N+\varepsilon,+\infty)\times K$.
--
--   This is the elementary convergence statement behind the convergence of the $\theta$-series $\sum_{\xi}f(\xi g)$ of Schwartz–Bruhat functions, uniformly for $g$ in compact sets.
--
--   **Formalization Note** $\mathbb R^N$ with a norm inducing the Euclidean topology is a real normed space of dimension $N$. Convergence is unconditional convergence of the net of finite partial sums.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 2, §2.2.1, Proposition 2.2.1.3, eq. (2.2.1.3), p. 76

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem lattice_sum_uniform_convergence
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Γ : Submodule ℤ E) [DiscreteTopology Γ] [IsZLattice ℝ Γ] (K : Set E) (hK : IsCompact K) :
    (∀ σ : ℝ, (Module.finrank ℝ E : ℝ) < σ →
      ∃ S : E → ℝ, TendstoUniformlyOn
        (fun (s : Finset {ξ : Γ // (ξ : E) ∉ K}) (x : E) =>
          ∑ ξ ∈ s, ‖((ξ : Γ) : E) + x‖ ^ (-σ))
        S Filter.atTop K) ∧
    (∀ ε : ℝ, 0 < ε → ∃ S : ℝ × E → ℝ, TendstoUniformlyOn
      (fun (s : Finset {ξ : Γ // (ξ : E) ∉ K}) (p : ℝ × E) =>
        ∑ ξ ∈ s, ‖((ξ : Γ) : E) + p.2‖ ^ (-p.1))
      S Filter.atTop (Set.Ici ((Module.finrank ℝ E : ℝ) + ε) ×ˢ K)) := by sorry

end MasulloGRH
