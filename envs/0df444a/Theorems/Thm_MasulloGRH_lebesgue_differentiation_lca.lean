-- Prove2me | Theorems.Thm_MasulloGRH_lebesgue_differentiation_lca
-- name    : MasulloGRH.lebesgue_differentiation_lca
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:39:41.969387+00:00
-- url     : https://prove2.me/theorems/98e5565a-8bc2-40f0-b91d-857aa86b65aa
-- title:
--   Theorem A.5.4.1 (2)–(3) — Lebesgue's Differentiation Theorem on a locally compact abelian group
-- statement:
--   Let $G$ be a Hausdorff, locally compact, second countable abelian group with a Haar measure $\mu_G$. A sequence $(U_k)_{k\ge0}$ of $\mu_G$-measurable subsets of $G$ containing the neutral element is a **D-sequence** with constant $C>0$ if $0<\mu_G(U_k)<\infty$, $U_{k+1}\subset U_k$ and $0<\mu_G(U_kU_k^{-1})<C\,\mu_G(U_k)$ for all $k$; it is a **D′-sequence** if moreover every neighbourhood of the neutral element contains some $U_k$.
--
--   Let $(U_k)$ be a D′-sequence in $G$ and let $f\colon G\to\mathbb C$ be locally integrable. Then for $\mu_G$-almost every $x\in G$ the averages of $f$ over the translates $xU_k$ converge to $f(x)$:
--
--   $$f(x)=\lim_{k\to+\infty}\frac{1}{\mu_G(U_k)}\int_{xU_k}f(y)\,d\mu_G(y)\qquad\text{for }\mu_G\text{-almost every }x\in G .$$
--
--   In particular the set of points at which the averages do not converge is $\mu_G$-negligible. The draft uses this on the idele class group to evaluate integral kernels along the diagonal.
--
--   **Formalization Note** This statement contains parts (2) and (3) of the source. Part (1), uniform continuity of each average for locally integrable $f$, is not included.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix A, §A.5.4, Theorem A.5.4.1 (Lebesgue's Differentiation Theorem - Hausdorff Locally Compact Abelian Groups), parts (2) and (3), eqs. (A.5.4.1)–(A.5.4.2), pp. 582–583

import Definitions.Def_MasulloGRH_DSequences

set_option autoImplicit false

namespace MasulloGRH

open MeasureTheory Pointwise

theorem lebesgue_differentiation_lca
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (U : ℕ → Set G) (C : ℝ) (hU : IsDPrimeSequence μ U C)
    (f : G → ℂ) (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Filter.Tendsto (fun k : ℕ => dAverage μ U f k x) Filter.atTop (nhds (f x)) := by sorry

end MasulloGRH
