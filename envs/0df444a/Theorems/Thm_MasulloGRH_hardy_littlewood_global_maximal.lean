-- Prove2me | Theorems.Thm_MasulloGRH_hardy_littlewood_global_maximal
-- name    : MasulloGRH.hardy_littlewood_global_maximal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:39:22.869579+00:00
-- url     : https://prove2.me/theorems/5b749d15-aeeb-4a63-bcde-00e8cce617ec
-- title:
--   Theorem A.5.3.7 — Hardy–Littlewood Global Maximal Theorem on a locally compact abelian group
-- statement:
--   Let $G$ be a Hausdorff, locally compact, second countable abelian group with a Haar measure $\mu_G$. A sequence $(U_k)_{k\ge0}$ of $\mu_G$-measurable subsets of $G$ containing the neutral element is a **D-sequence** with constant $C>0$ if $0<\mu_G(U_k)<\infty$, $U_{k+1}\subset U_k$ and $0<\mu_G(U_kU_k^{-1})<C\,\mu_G(U_k)$ for all $k$; it is a **D′-sequence** if moreover every neighbourhood of the neutral element contains some $U_k$.
--
--   Let $(U_k)$ be a D′-sequence with constant $C$ such that the closure of $U_0$ is compact, let $f\colon G\to\mathbb C$ be locally integrable, and let
--   $$(Mf)(x)=\limsup_{k\ge0}\frac{1}{\mu_G(U_k)}\int_{xU_k}|f(y)|\,d\mu_G(y)$$
--   be its maximal function. Then:
--
--   1. If $f\in L^1(G,\mu_G)$, then for every real $\alpha>0$
--   $$\mu_G\big(\{x\in G:(Mf)(x)>\alpha\}\big)\le\frac{2C}{\alpha}\,\|f\|_{L^1(G,\mu_G)} .$$
--   2. If $p>1$ is real and $f\in L^p(G,\mu_G)$, then $Mf$ is measurable and
--   $$\int_G(Mf)(x)^p\,d\mu_G(x)\le\frac{C\,p^{p+1}}{(p-1)^p}\,\|f\|^p_{L^p(G,\mu_G)} ,$$
--   so $Mf\in L^p(G,\mu_G)$.
--
--   The weak-type $(1,1)$ bound and the $L^p$ bound for the maximal function are the inputs for Lebesgue differentiation along D′-sequences, which the draft applies on idele groups and idele class groups.
--
--   **Formalization Note** The maximal function takes values in $[0,\infty]$ and the integrals are integrals of non-negative extended real functions. Measurability of $Mf$ is stated as almost-everywhere measurability.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix A, §A.5.3, Theorem A.5.3.7 (Hardy-Littlewood Global Maximal Theorem), eqs. (A.5.3.16)–(A.5.3.18), p. 582

import Definitions.Def_MasulloGRH_DSequences

set_option autoImplicit false

namespace MasulloGRH

open MeasureTheory Pointwise

theorem hardy_littlewood_global_maximal
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (U : ℕ → Set G) (C : ℝ) (hU : IsDPrimeSequence μ U C)
    (hU0 : IsCompact (closure (U 0))) (f : G → ℂ) (hf : LocallyIntegrable f μ) :
    (Integrable f μ → ∀ α : ℝ, 0 < α →
      μ {x : G | ENNReal.ofReal α < dMaximal μ U f x} ≤
        ENNReal.ofReal (2 * C / α) * ∫⁻ x, ‖f x‖ₑ ∂μ) ∧
    (∀ p : ℝ, 1 < p → MemLp f (ENNReal.ofReal p) μ →
      AEMeasurable (dMaximal μ U f) μ ∧
      ∫⁻ x, dMaximal μ U f x ^ p ∂μ ≤
        ENNReal.ofReal (C * p ^ (p + 1) / (p - 1) ^ p) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) := by sorry

end MasulloGRH
