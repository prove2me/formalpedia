-- Prove2me | Theorems.Thm_MasulloRepair_nuclear_comp_right_adjoint_sot_tendsto_traceNorm
-- name    : MasulloRepair.nuclear_comp_right_adjoint_sot_tendsto_traceNorm
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:17:16.272944+00:00
-- url     : https://prove2.me/theorems/ffc89412-6e81-4f09-bcfa-656a3cc0d5bb
-- title:
--   Bounded strong convergence $Q_i^*\to Q^*$ and $T$ nuclear imply $\|TQ_i-TQ\|_{\mathrm{Tr}}\to0$ and $\operatorname{Trace}(TQ_i)\to\operatorname{Trace}(TQ)$
-- statement:
--   This is the right-multiplication form of the strong-to-trace-norm convergence principle of Masullo's manuscript (Lemma C.3.4.4(5), p. 698; Corollary C.3.5.5(2),(3), p. 702). It identifies the correct limit in Theorem 11.2.1.2(2) (p. 488), where a nuclear operator is multiplied on the right by orthogonal projections that converge strongly to a projection different from the identity.
--
--   Let $H$ be a complex Hilbert space and let $T$ be a nuclear (trace-class) operator on $H$. Let $(Q_i)_{i\in I}$ be a family of bounded operators on $H$ indexed along a filter $l$ on $I$, and let $Q$ be a bounded operator. Assume that
--
--   1. there is a constant $C$ with $\|Q_i\|\le C$ for $l$-eventually all $i$;
--   2. the adjoints converge strongly: $Q_i^*u\to Q^*u$ in $H$ for every $u\in H$.
--
--   Then every $TQ_i$ and $TQ$ is nuclear, and
--
--   $$
--   \lim_{i}\ \|TQ_i-TQ\|_{\mathrm{Tr}}=0,\qquad \lim_{i}\ \operatorname{Trace}(TQ_i)=\operatorname{Trace}(TQ).
--   $$
--
--   In particular, if the $Q_i$ are self-adjoint (for instance orthogonal projections) and $Q_i\to Q$ strongly, the trace-norm limit of $TQ_i$ is $TQ$; it equals $T$ only when $T(1-Q)=0$. Strong convergence of the $Q_i$ themselves is not sufficient for the trace-norm convergence of $TQ_i$ (take $Q_iu=\langle u,e_i\rangle e_0$ on $\ell^2$ and $T=\langle\cdot,e_0\rangle e_0$), which is why hypothesis 2 is placed on the adjoints.
--
--   **Formalization Note** Nuclearity, the trace and the trace norm are the platform definitions `IsNuclearOperator`, `operatorTrace` and `traceNorm` of `Def_MasulloGRH_HilbertNuclear` (Definition C.3.4.2 of the manuscript); the adjoint is Mathlib's `ContinuousLinearMap.adjoint`. The limit is taken along an arbitrary filter `l`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Lemma C.3.4.4(5), p. 698, and Corollary C.3.5.5(2),(3), p. 702 (generalized); used in Theorem 11.2.1.2(2), p. 488

import Definitions.Def_MasulloGRH_HilbertNuclear

set_option autoImplicit false

open Filter Topology MasulloGRH

theorem MasulloRepair.nuclear_comp_right_adjoint_sot_tendsto_traceNorm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : IsNuclearOperator T)
    {ι : Type*} (l : Filter ι) (Q : ι → H →L[ℂ] H) (Q₀ : H →L[ℂ] H) (C : ℝ)
    (hbd : ∀ᶠ i in l, ‖Q i‖ ≤ C)
    (hQ : ∀ u : H, Tendsto (fun i => ContinuousLinearMap.adjoint (Q i) u) l
      (𝓝 (ContinuousLinearMap.adjoint Q₀ u))) :
    (∀ i, IsNuclearOperator (T ∘L Q i)) ∧ IsNuclearOperator (T ∘L Q₀) ∧
    Tendsto (fun i => traceNorm (T ∘L Q i - T ∘L Q₀)) l (𝓝 0) ∧
    Tendsto (fun i => operatorTrace (T ∘L Q i)) l (𝓝 (operatorTrace (T ∘L Q₀))) := by sorry
