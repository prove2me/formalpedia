-- Prove2me | Theorems.Thm_MasulloGRH_dPrimeSequence_measure_maximal_compact
-- name    : MasulloGRH.dPrimeSequence_measure_maximal_compact
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:13.195687+00:00
-- url     : https://prove2.me/theorems/ed7512e0-a96a-4390-907d-dcd5899f3062
-- title:
--   Theorem A.5.3.5 — maximal inequality on compact sets for a Radon measure along a D′-sequence: $\mu_G(K\cap\{M\nu>\alpha\})\le\frac C\alpha\,\nu(K)$
-- statement:
--   **Measure-theoretic maximal theorem along a D′-sequence (Hewitt–Ross).** Let $G$ be a Hausdorff locally compact abelian group with a Haar measure $\mu_G$. A sequence $(U_k)_{k\ge0}$ of $\mu_G$-measurable subsets of $G$ containing the neutral element is a **D-sequence** with structural constant $C>0$ if for all $k\ge 0$: $0<\mu_G(U_k)<\infty$, $U_{k+1}\subset U_k$, and $0<\mu_G(U_kU_k^{-1})<C\,\mu_G(U_k)$. It is a **D′-sequence** if moreover every neighbourhood of the neutral element contains some $U_k$.
--
--   Assume in addition that $G$ is second countable. Let $(U_k)_{k\ge0}$ be a D′-sequence in $G$ with structural constant $C$, and let $\nu$ be a positive Radon measure on $G$. Define
--   $$(M\nu)(x)\;=\;\limsup_{k\to\infty}\frac{\nu(xU_k)}{\mu_G(U_k)}\ \in[0,\infty],\qquad x\in G .$$
--   Then for every compact subset $K\subset G$ and every real number $\alpha>0$
--   $$\mu_G\big(K\cap\{x\in G:\ (M\nu)(x)>\alpha\}\big)\;\le\;\frac{C}{\alpha}\,\nu(K).$$
--
--   Compared with the inequality for general D-sequences, where the right-hand side involves $\nu$ of the enlarged set $(K\cap\{M\nu>\alpha\})\cdot U_0$, the shrinking of the $U_k$ to the neutral element allows one to replace it by $\nu(K)$ itself. This is the form of the weak type inequality that yields Lebesgue's differentiation theorem along D′-sequences (Theorem A.5.4.1 of the source), used there on idele groups and idele class groups.
--
--   **Formalization Note.** D′-sequences are the platform notion `MasulloGRH.IsDPrimeSequence μ U C`; as in the source the sets $U_k$ are only assumed $\mu_G$-measurable (not Borel), and $\nu(xU_k)$ is then the outer measure of the translate. A positive Radon measure is a Borel measure with `Measure.Regular`. The upper limit is `Filter.limsup` along $k\to\infty$ in $[0,\infty]$; the left-hand side is the outer Haar measure of the set, which is not claimed to be measurable. The source writes $\overline M\nu$ for the same function $M\nu$ as in Theorem A.5.3.4.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 580, Theorem A.5.3.5, eqs. (A.5.3.5)-(A.5.3.6) (proof on pp. 580-581); classical reference: E. Hewitt and K. A. Ross, Abstract Harmonic Analysis, Vol. II, Springer-Verlag, 1970, Ch. XI, Thm. 44.14, p. 641 (of which the paper says this is a special case)

import Mathlib
import Definitions.Def_MasulloGRH_DSequences

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace MasulloGRH

theorem dPrimeSequence_measure_maximal_compact
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (U : ℕ → Set G) (C : ℝ) (hU : IsDPrimeSequence μ U C)
    (ν : Measure G) [ν.Regular] (K : Set G) (hK : IsCompact K) (α : ℝ) (hα : 0 < α) :
    μ (K ∩ {x | ENNReal.ofReal α < limsup (fun k : ℕ => ν (x • U k) / μ (U k)) atTop}) ≤
      ENNReal.ofReal (C / α) * ν K := by sorry

end MasulloGRH
