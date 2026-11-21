-- Prove2me | Theorems.Thm_MasulloGRH_tendstoUniformlyOn_bilinear_series
-- name    : MasulloGRH.tendstoUniformlyOn_bilinear_series
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:12:48.605211+00:00
-- url     : https://prove2.me/theorems/cf8e14be-6bd2-4e8a-b969-083ded74c247
-- title:
--   Nuclear bilinear series converge uniformly on products of bounded sets
-- statement:
--   Let $E$, $F$ be complex vector spaces with topologies, $(\varphi_m)_{m\ge0}$ an equicontinuous sequence of continuous linear functionals on $E$, $(\psi_m)_{m\ge0}$ an equicontinuous sequence of continuous linear functionals on $F$, and $(\lambda_m)_{m\ge0}$ complex numbers with $\sum_m|\lambda_m|<\infty$. Suppose a function $B\colon E\times F\to\mathbb C$ satisfies
--
--   $$B(x,y)=\sum_{m\ge0}\lambda_m\,\varphi_m(x)\,\psi_m(y)\qquad\text{for all }x,y .$$
--
--   Then for all bounded subsets $S\subseteq E$ and $T\subseteq F$, the partial sums $\sum_{m<k}\lambda_m\varphi_m(x)\psi_m(y)$ converge to $B(x,y)$ uniformly on $S\times T$ as $k\to\infty$.
--
--   This upgrades pointwise convergence of a nuclear series to the uniform convergence on bounded sets required in the Schwartz kernel theorem: equicontinuous families of functionals are uniformly bounded on bounded sets, so the Weierstrass test applies.
--
--   **Formalization Note** Boundedness is von Neumann boundedness (`Bornology.IsVonNBounded ℂ`).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Theorem C.2.4.18 (Schwartz kernel theorem) and its proof; cf. Trèves, Topological Vector Spaces, Distributions and Kernels, Ch. 50 (Theorem 50.1 and Proposition 50.5)

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem tendstoUniformlyOn_bilinear_series (E F : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (φ : ℕ → StrongDual ℂ E) (ψ : ℕ → StrongDual ℂ F) (c : ℕ → ℂ)
    (hφ : Equicontinuous (fun m => (φ m : E → ℂ))) (hψ : Equicontinuous (fun m => (ψ m : F → ℂ)))
    (hc : Summable (fun m => ‖c m‖)) (B : E → F → ℂ)
    (hsum : ∀ x y, HasSum (fun m => c m * φ m x * ψ m y) (B x y))
    (S : Set E) (T : Set F) (hS : Bornology.IsVonNBounded ℂ S)
    (hT : Bornology.IsVonNBounded ℂ T) :
    TendstoUniformlyOn
      (fun (k : ℕ) (p : E × F) => ∑ m ∈ Finset.range k, c m * φ m p.1 * ψ m p.2)
      (fun p : E × F => B p.1 p.2) Filter.atTop (S ×ˢ T) := by sorry

end MasulloGRH
