-- Prove2me | Theorems.Thm_MasulloGRH_dSequence_measure_maximal_ae_lt_top
-- name    : MasulloGRH.dSequence_measure_maximal_ae_lt_top
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:23.441805+00:00
-- url     : https://prove2.me/theorems/7b81c65d-3d00-4015-9302-df141fb465d7
-- title:
--   Theorem A.5.3.4(2) — along a Borel D-sequence with $\overline{U_0}$ compact, the maximal function $M\nu$ of a Radon measure is finite almost everywhere
-- statement:
--   **Measure-theoretic maximal theorem along a D-sequence (Hewitt–Ross), part (2): finiteness almost everywhere.** Let $G$ be a Hausdorff locally compact abelian group with a Haar measure $\mu_G$. A sequence $(U_k)_{k\ge0}$ of $\mu_G$-measurable subsets of $G$ containing the neutral element is a **D-sequence** with structural constant $C>0$ if for all $k\ge 0$: $0<\mu_G(U_k)<\infty$, $U_{k+1}\subset U_k$, and $0<\mu_G(U_kU_k^{-1})<C\,\mu_G(U_k)$. It is a **D′-sequence** if moreover every neighbourhood of the neutral element contains some $U_k$.
--
--   Assume in addition that $G$ is second countable. Let $(U_k)_{k\ge0}$ be a D-sequence in $G$ all of whose members are Borel sets and such that the closure $\overline{U_0}$ is compact, and let $\nu$ be a positive Radon measure on $G$. Then the maximal function
--   $$(M\nu)(x)\;=\;\limsup_{k\to\infty}\frac{\nu(xU_k)}{\mu_G(U_k)}\ \in[0,\infty],\qquad x\in G ,$$
--   is finite $\mu_G$-almost everywhere:
--   $$\mu_G\big(\{x\in G:\ (M\nu)(x)=\infty\}\big)=0 .$$
--
--   This is the qualitative consequence of the weak type inequality of part (1): the upper derivative of a Radon measure with respect to Haar measure along the sequence is finite almost everywhere. In the source it accompanies the weak type inequality of part (1), from which the maximal theorems along D-sequences and D′-sequences (Theorems A.5.3.5 and A.5.3.6 of the source) are derived.
--
--   **Formalization Note.** D-sequences are the platform notion `MasulloGRH.IsDSequence μ U C`; the Borel hypothesis is `∀ k, MeasurableSet (U k)`; a positive Radon measure is a Borel measure with `Measure.Regular`. The upper limit is `Filter.limsup` along $k\to\infty$ in $[0,\infty]$, and "almost everywhere" is with respect to the Haar measure.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 579-580, Theorem A.5.3.4(2), eq. (A.5.3.2); classical reference: E. Hewitt and K. A. Ross, Abstract Harmonic Analysis, Vol. II, Springer-Verlag, 1970, Ch. XI, §44, Thm. 44.13, p. 640 (of which the paper says this is a special case)

import Mathlib
import Definitions.Def_MasulloGRH_DSequences

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace MasulloGRH

theorem dSequence_measure_maximal_ae_lt_top
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (U : ℕ → Set G) (C : ℝ) (hU : IsDSequence μ U C)
    (hBorel : ∀ k, MeasurableSet (U k)) (hU0 : IsCompact (closure (U 0)))
    (ν : Measure G) [ν.Regular] :
    ∀ᵐ x ∂μ, limsup (fun k : ℕ => ν (x • U k) / μ (U k)) atTop < ⊤ := by sorry

end MasulloGRH
