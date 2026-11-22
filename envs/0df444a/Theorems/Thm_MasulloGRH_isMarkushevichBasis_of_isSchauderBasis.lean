-- Prove2me | Theorems.Thm_MasulloGRH_isMarkushevichBasis_of_isSchauderBasis
-- name    : MasulloGRH.isMarkushevichBasis_of_isSchauderBasis
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:49:37.138327+00:00
-- url     : https://prove2.me/theorems/5dd54d80-1122-45d5-8fce-dfe469c678a9
-- title:
--   A Schauder basis of a Hausdorff locally convex space, with its coefficient functionals, is a Markushevich basis
-- statement:
--   **Schauder bases are Markushevich bases.** Let $E$ be a Hausdorff locally convex topological $\mathbb C$-vector space and let $(x_m)_{m\ge0}$ be a Schauder basis of $E$ with continuous coefficient functionals $(f_m)_{m\ge0}\subset E'$, i.e. $f_m(x_n)=\delta_{mn}$ for all $m,n\ge 0$ and
--   $$u=\sum_{m\ge0}f_m(u)\,x_m=\lim_{k\to\infty}\sum_{m=0}^{k}f_m(u)\,x_m\qquad(u\in E).$$
--   Then $\{(x_m,f_m)\}_{m\ge0}$ is a Markushevich basis of $E$: the system is biorthogonal, the linear span of the $x_m$ is dense in $E$, and the functionals $f_m$ separate the points of $E$.
--
--   The paper records this fact on p. 312 (with a reference to Jarchow) and uses it at the opening of §10.2 (p. 438), where the Schauder bases constructed in the previous chapters are to survive, as Markushevich bases, the passage to coarser Hilbert–Sobolev topologies. The statement connects the platform's notion of Schauder basis in locally convex spaces with the notion of Markushevich basis.
--
--   **Formalization Note.** Schauder bases are the platform's `MasulloGRH.IsSchauderBasis` (Definition 4.1.1.1 of the paper: biorthogonality and convergence of the basic projections $\sum_{m\le k}f_m(u)x_m\to u$), Hausdorff local convexity is `MasulloGRH.IsHLCS`, and Markushevich bases are `MarkushevichBasis.IsMarkushevichBasis` with index set $\mathbb N$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 312 (introduction to Chapter 7) and p. 438, §10.2 (opening paragraph); classical reference: H. Jarchow, Locally Convex Spaces, B. G. Teubner, Stuttgart, 1981, Part II, Ch. 14, §14.2, Prop. 1, p. 292 (as cited by the paper on p. 312)

import Definitions.Def_MasulloGRH_SchauderBases
import Definitions.Def_MarkushevichBasis_Basic

set_option autoImplicit false

namespace MasulloGRH

theorem isMarkushevichBasis_of_isSchauderBasis
    (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (x : ℕ → E) (f : ℕ → StrongDual ℂ E) (hx : IsSchauderBasis x f) :
    MarkushevichBasis.IsMarkushevichBasis x f := by sorry

end MasulloGRH
