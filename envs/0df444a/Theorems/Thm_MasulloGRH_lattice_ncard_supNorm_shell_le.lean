-- Prove2me | Theorems.Thm_MasulloGRH_lattice_ncard_supNorm_shell_le
-- name    : MasulloGRH.lattice_ncard_supNorm_shell_le
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T16:39:22.45486+00:00
-- url     : https://prove2.me/theorems/a7a4ed6c-2e36-42c5-8753-893cc3d01f8e
-- title:
--   Lemma 2.2.1.1 — a full lattice $\Gamma\subset\mathbb R^N$ has $O_{\Gamma,N}(r^{N-1})$ points in the shell $r\le\|\xi\|_\infty<r+1$
-- statement:
--   **Lattice points in a cubical shell** (Lemma 2.2.1.1 of the source).
--
--   Let $N\ge1$ be an integer and $\Gamma\subset\mathbb R^N$ a full lattice, i.e. a discrete subgroup spanning $\mathbb R^N$ over $\mathbb R$. Let $\|x\|_\infty=\max_{1\le i\le N}|x_i|$ be the sup norm and, for a real number $r\ge1$, let
--   $$X_r=\{x\in\mathbb R^N:\ r\le\|x\|_\infty<r+1\}$$
--   be the shell between the cubes of half-side $r$ and $r+1$.
--
--   Then $\Gamma\cap X_r$ is finite and there is a constant $C$, depending only on $N$ and $\Gamma$, such that for all $r\ge1$
--   $$|\Gamma\cap X_r|\le C\,r^{N-1}.$$
--
--   The exponent $N-1$ is the order of growth of the volume of the shell, $\mathrm{vol}(X_r)=(2(r+1))^N-(2r)^N=2^NNr^{N-1}+O_N(r^{N-2})$. The source uses this count, by summation over the shells, to prove the uniform convergence, for $\sigma>N$ and $x$ in a compact set $K\subset\mathbb R^N$, of the lattice sums $\sum_{\xi\in\Gamma\setminus(-K)}\|\xi+x\|^{-\sigma}$ (Proposition 2.2.1.3, where the excluded set is printed as $\Gamma\cap K$), which in turn controls the adelic theta series $\sum_{\xi\in F^\times}f(\xi g)$.
--
--   **Formalization Note.** $\mathbb R^N$ is `Fin N → ℝ`, whose norm is the sup norm; $\Gamma$ is a `Submodule ℤ (Fin N → ℝ)` with `DiscreteTopology` and `IsZLattice ℝ`. The estimate "$O_{\Gamma,N}(r^{N-1})$ as $r\to+\infty$" of the source is stated with one constant for all $r\ge1$, which is equivalent since the counts are uniformly bounded for $r$ in any bounded range and $r^{N-1}\ge1$. The assertions of the source that $X_r$ is bounded and Lebesgue measurable are immediate and are not restated.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 75, Lemma 2.2.1.1, eqs. (2.2.1.1)–(2.2.1.2); classical reference cited there (Remark 2.2.1.2 and proof): W. M. Schmidt, Northcott's Theorem on heights II. The quadratic case, Acta Arithmetica LXX.4 (1995), Lemma 1, p. 347

import Mathlib

set_option autoImplicit false

namespace MasulloGRH

theorem lattice_ncard_supNorm_shell_le
    (N : ℕ) (hN : 1 ≤ N) (Γ : Submodule ℤ (Fin N → ℝ)) [DiscreteTopology Γ] [IsZLattice ℝ Γ] :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      {ξ : Fin N → ℝ | ξ ∈ Γ ∧ r ≤ ‖ξ‖ ∧ ‖ξ‖ < r + 1}.Finite ∧
      ({ξ : Fin N → ℝ | ξ ∈ Γ ∧ r ≤ ‖ξ‖ ∧ ‖ξ‖ < r + 1}.ncard : ℝ) ≤ C * r ^ (N - 1) := by sorry

end MasulloGRH
