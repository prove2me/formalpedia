-- Prove2me | Theorems.Thm_MasulloGRH_frechet_isSchauderBasis_of_existsUnique_expansion
-- name    : MasulloGRH.frechet_isSchauderBasis_of_existsUnique_expansion
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:01:01.046271+00:00
-- url     : https://prove2.me/theorems/e12f0bf8-c236-4619-82f0-9da3fe0fb442
-- title:
--   In a Fréchet space every topological basis (unique series expansions) is a Schauder basis: the coefficient functionals are continuous
-- statement:
--   **In a Fréchet space every topological basis is a Schauder basis.** Let $E$ be a complex Fréchet space (a complete metrizable Hausdorff locally convex space) and let $(x_m)_{m\ge0}$ be a sequence in $E$ such that every $u\in E$ has a **unique** expansion
--   $$u=\sum_{m\ge0}a_m\,x_m,\qquad\text{i.e. }\ \sum_{m=0}^{k}a_m\,x_m\xrightarrow[k\to\infty]{}u\ \text{ in }E,$$
--   with scalars $a_m=a_m(u)\in\mathbb C$. Then there are continuous linear functionals $f_m\in E'$ such that $(x_m)$ is a Schauder basis of $E$ with coefficient functionals $(f_m)$ in the sense of Definition 4.1.1.1(2):
--   $$f_m(x_n)=\delta_{m,n}\quad(m,n\ge0),\qquad u=\sum_{m\ge0}f_m(u)\,x_m\quad(u\in E);$$
--   necessarily $f_m=a_m$, so the coefficient functionals of the topological basis are automatically continuous.
--
--   This is the Fréchet-space form of Banach's theorem on coefficient functionals. It shows that, for the Fréchet spaces considered in the paper, the distinction drawn before Definition 4.1.1.1 between *topological bases* and *Schauder bases* disappears, provided topological bases are understood in the classical sense of unique expansions.
--
--   **Deviation from the source.** The paper's Definition 4.1.1.1(1) does not ask for uniqueness: it calls $(x_m)$ a topological basis of $E$ as soon as there are merely algebraic linear functionals $f_m\in E^*$ with $f_m(x_n)=\delta_{m,n}$ and $u=\sum_m f_m(u)x_m$ for all $u$. With that literal definition a topological basis need not be a Schauder basis, even in a Hilbert space: in $\ell^2$, with unit vectors $(e_k)_{k\ge1}$, take $x_0=\sum_{k\ge1}k^{-1}e_k$, $x_k=e_k$ $(k\ge1)$, a (necessarily discontinuous) linear functional $f_0$ with $f_0(x_0)=1$ and $f_0(e_k)=0$ for all $k\ge1$, and $f_k(u)=u_k-k^{-1}f_0(u)$, where $u_k$ denotes the $k$-th coordinate of $u\in\ell^2$. The statement here uses the classical notion (every vector has a *unique* expansion), for which the coefficient functionals are automatically continuous.
--
--   **Formalization Note.** Uses the platform notions `MasulloGRH.IsFrechet` (locally convex, complete Hausdorff, metrizable) and `MasulloGRH.IsSchauderBasis` (biorthogonality and convergence of the partial sums over $0\le m\le k$, coefficient functionals in `StrongDual ℂ E`). The hypothesis is the classical one (existence and uniqueness of the expansion of every vector); uniqueness cannot be dropped: the paper's Definition 4.1.1.1(1), with merely algebraic biorthogonal functionals, is strictly weaker (see the deviation remark). The converse implication (a Schauder basis gives unique expansions) is elementary.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 157, Definition 4.1.1.1 and the preceding paragraph (topological bases versus Schauder bases; the paper refers to H. Jarchow, Locally Convex Spaces, Teubner, 1981, Part II, Ch. 14, §14.2, p. 292, for these notions)

import Definitions.Def_MasulloGRH_SchauderBases

open Filter Topology

set_option autoImplicit false

namespace MasulloGRH

theorem frechet_isSchauderBasis_of_existsUnique_expansion
    (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hF : IsFrechet E) (x : ℕ → E)
    (hx : ∀ u : E, ∃! a : ℕ → ℂ,
      Tendsto (fun k => ∑ m ∈ Finset.range (k + 1), a m • x m) atTop (𝓝 u)) :
    ∃ f : ℕ → StrongDual ℂ E, IsSchauderBasis x f := by sorry

end MasulloGRH
