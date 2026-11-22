-- Prove2me | Theorems.Thm_MasulloGRH_traceNorm_norm_properties
-- name    : MasulloGRH.traceNorm_norm_properties
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:29.614859+00:00
-- url     : https://prove2.me/theorems/c075a60f-96bd-48c4-b2db-1a0b79feaa48
-- title:
--   Lemma C.3.4.4(1),(3) — $\|\cdot\|_{\mathrm{Tr}}$ is a norm on $N(H)$, the trace is linear and $|\operatorname{Trace}(T)|\le\|T\|_{\mathrm{Tr}}$
-- statement:
--   **The trace norm is a norm on the nuclear operators, and the trace is a continuous linear functional of norm at most one.**
--
--   Let $H$ be a complex Hilbert space and $N(H)$ the set of nuclear (trace-class) operators on $H$, i.e. of the bounded operators of the form $Tu=\sum_m\langle u,x_m\rangle y_m$ with $\sum_m\|x_m\|\|y_m\|<\infty$. For $T\in N(H)$ and an orthonormal basis $\Sigma$ of $H$ put
--   $$\operatorname{Trace}(T)=\sum_{\phi\in\Sigma}\langle T\phi,\phi\rangle_H,\qquad\|T\|_{\mathrm{Tr}}=\operatorname{Trace}(|T|),\quad|T|=(T^*T)^{1/2}.$$
--
--   Let $S,T\in N(H)$ and $a\in\mathbb C$. Then:
--
--   1. $S+T$ and $aT$ are nuclear, so $N(H)$ is a linear subspace of $\mathscr B(H)$;
--   2. $\|\cdot\|_{\mathrm{Tr}}$ is a norm on $N(H)$:
--   $$\|S+T\|_{\mathrm{Tr}}\le\|S\|_{\mathrm{Tr}}+\|T\|_{\mathrm{Tr}},\qquad\|aT\|_{\mathrm{Tr}}=|a|\,\|T\|_{\mathrm{Tr}},\qquad\|T\|_{\mathrm{Tr}}\ge0,\qquad\|T\|_{\mathrm{Tr}}=0\iff T=0;$$
--   3. the trace is linear on $N(H)$ and bounded by the trace norm:
--   $$\operatorname{Trace}(S+T)=\operatorname{Trace}(S)+\operatorname{Trace}(T),\qquad\operatorname{Trace}(aT)=a\operatorname{Trace}(T),\qquad|\operatorname{Trace}(T)|\le\|T\|_{\mathrm{Tr}} .$$
--
--   Hence $(N(H),\|\cdot\|_{\mathrm{Tr}})$ is a normed space and $\operatorname{Trace}:N(H)\to\mathbb C$ is continuous for the trace-norm topology; the paper uses this continuity to pass to the limit in traces of trace-norm convergent sequences (Proposition C.3.5.1, Corollary C.3.5.5).
--
--   **Formalization Note.** `IsNuclearOperator`, `operatorTrace` and `traceNorm` are from `Def_MasulloGRH_HilbertNuclear` (sums over one fixed orthonormal basis; for nuclear operators they do not depend on the basis). All assertions are made for nuclear $S$, $T$ only; outside $N(H)$ these expressions are junk values. In (C.3.4.4)(3) the paper prints $|\mathrm{Tr}(A)|\le\|A\|_r$, a misprint for $\|A\|_{\mathrm{Tr}}$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 698, Lemma C.3.4.4(1),(3); classical reference: J. Conway, A Course in Operator Theory, AMS (the paper's [Cnw-c]), Ch. 3, Thm. 18.11(a),(c)

import Mathlib
import Definitions.Def_MasulloGRH_HilbertNuclear

open Filter Topology MeasureTheory
set_option autoImplicit false

namespace MasulloGRH

theorem traceNorm_norm_properties {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (S T : H →L[ℂ] H) (hS : IsNuclearOperator S) (hT : IsNuclearOperator T) (a : ℂ) :
    IsNuclearOperator (S + T) ∧ IsNuclearOperator (a • T) ∧
      traceNorm (S + T) ≤ traceNorm S + traceNorm T ∧
      traceNorm (a • T) = ‖a‖ * traceNorm T ∧
      0 ≤ traceNorm T ∧ (traceNorm T = 0 ↔ T = 0) ∧
      operatorTrace (S + T) = operatorTrace S + operatorTrace T ∧
      operatorTrace (a • T) = a * operatorTrace T ∧
      ‖operatorTrace T‖ ≤ traceNorm T := by sorry

end MasulloGRH
