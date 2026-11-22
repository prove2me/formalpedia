-- Prove2me | Theorems.Thm_MasulloGRH_dSequence_measure_maximal_weak
-- name    : MasulloGRH.dSequence_measure_maximal_weak
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:18.81648+00:00
-- url     : https://prove2.me/theorems/57cbcccb-8b77-4c08-8eba-c34b7faef094
-- title:
--   Theorem A.5.3.4(1) — maximal inequality for a Radon measure along a Borel D-sequence: $\mu_G(E)\le\frac C\alpha\,\nu(E\cdot U_0)$ for $E=B\cap\{M\nu>\alpha\}$
-- statement:
--   **Measure-theoretic maximal theorem along a D-sequence (Hewitt–Ross), part (1).** Let $G$ be a Hausdorff locally compact abelian group with a Haar measure $\mu_G$. A sequence $(U_k)_{k\ge0}$ of $\mu_G$-measurable subsets of $G$ containing the neutral element is a **D-sequence** with structural constant $C>0$ if for all $k\ge 0$: $0<\mu_G(U_k)<\infty$, $U_{k+1}\subset U_k$, and $0<\mu_G(U_kU_k^{-1})<C\,\mu_G(U_k)$. It is a **D′-sequence** if moreover every neighbourhood of the neutral element contains some $U_k$.
--
--   Assume in addition that $G$ is second countable. Let $(U_k)_{k\ge0}$ be a D-sequence in $G$ with structural constant $C$ all of whose members are Borel sets, and let $\nu$ be a positive Radon measure on $G$. Define the maximal function of $\nu$ by
--   $$(M\nu)(x)\;=\;\limsup_{k\to\infty}\frac{\nu(xU_k)}{\mu_G(U_k)}\ \in[0,\infty],\qquad x\in G .$$
--   Let $B\subset G$ be a $\mu_G$-measurable set with $\mu_G(B\cdot U_0)<\infty$, let $\alpha>0$ be a real number, and put
--   $$E\;=\;B\cap\{x\in G:\ (M\nu)(x)>\alpha\}.$$
--   Then
--   $$\mu_G(E)\;\le\;\frac{C}{\alpha}\,\nu\big(E\cdot U_0\big),$$
--   and equality holds if and only if $E=\varnothing$.
--
--   This is the weak type inequality for the "derivative" of a Radon measure with respect to Haar measure along a D-sequence; applied to $\nu=|f|\,\mu_G$ it gives the Hardy–Littlewood maximal inequalities on $G$ (Theorems A.5.3.6 and A.5.3.7 of the source), which the source uses on idele groups and idele class groups.
--
--   **Formalization Note.** D-sequences are the platform notion `MasulloGRH.IsDSequence μ U C`; "Borel D-sequence" is the extra hypothesis that every `U k` is a `MeasurableSet`. A positive Radon measure is a Borel measure with `Measure.Regular` (finite on compact sets, outer regular, inner regular on open sets). The upper limit is `Filter.limsup` along $k\to\infty$ of the extended real quotients $\nu(xU_k)/\mu_G(U_k)$, so $\nu(xU_k)=\infty$ is allowed. The sets $E$ and $E\cdot U_0$ are not claimed to be measurable: their measures are outer measures. The set $E$ is introduced through the hypothesis `hE` to avoid repeating its definition.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 579-580, Theorem A.5.3.4(1), eqs. (A.5.3.2)-(A.5.3.3); classical reference: E. Hewitt and K. A. Ross, Abstract Harmonic Analysis, Vol. II, Springer-Verlag, 1970, Ch. XI, §44, Thm. 44.13, p. 640 (of which the paper says this is a special case)

import Mathlib
import Definitions.Def_MasulloGRH_DSequences

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace MasulloGRH

theorem dSequence_measure_maximal_weak
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (U : ℕ → Set G) (C : ℝ) (hU : IsDSequence μ U C)
    (hBorel : ∀ k, MeasurableSet (U k)) (ν : Measure G) [ν.Regular]
    (B : Set G) (hB : NullMeasurableSet B μ) (hBU : μ (B * U 0) < ⊤) (α : ℝ) (hα : 0 < α)
    (E : Set G)
    (hE : E = B ∩ {x | ENNReal.ofReal α < limsup (fun k : ℕ => ν (x • U k) / μ (U k)) atTop}) :
    μ E ≤ ENNReal.ofReal (C / α) * ν (E * U 0) ∧
      (μ E = ENNReal.ofReal (C / α) * ν (E * U 0) ↔ E = ∅) := by sorry

end MasulloGRH
