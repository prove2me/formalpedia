-- Prove2me | Theorems.Thm_MasulloRepair_nuclear_comp_left_sot_tendsto_traceNorm
-- name    : MasulloRepair.nuclear_comp_left_sot_tendsto_traceNorm
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:17:11.770681+00:00
-- url     : https://prove2.me/theorems/1a5a042f-c18e-4e0b-9cc6-aac9ac32d33d
-- title:
--   Bounded strong convergence $Q_i\to Q$ and $T$ nuclear imply $\|Q_iT-QT\|_{\mathrm{Tr}}\to0$ and $\operatorname{Trace}(Q_iT)\to\operatorname{Trace}(QT)$
-- statement:
--   This is the general form of the strong-to-trace-norm convergence principle that Masullo's manuscript states only for finite-rank operators (Lemma C.3.4.4(5), p. 698) and for exhaustive filtrations by orthogonal projections (Corollary C.3.5.5, p. 702). It confirms those statements and extends them to the form needed in Chapters 10 and 11.
--
--   Let $H$ be a complex Hilbert space and let $T$ be a nuclear (trace-class) operator on $H$, i.e. $Tu=\sum_m\langle u,x_m\rangle y_m$ with $\sum_m\|x_m\|\,\|y_m\|<\infty$. Let $(Q_i)_{i\in I}$ be a family of bounded operators on $H$ indexed along a filter $l$ on $I$ (a sequence, a net, or a real parameter tending to $+\infty$), and let $Q$ be a bounded operator. Assume that
--
--   1. the family is eventually uniformly bounded: there is a constant $C$ with $\|Q_i\|\le C$ for $l$-eventually all $i$;
--   2. $Q_i\to Q$ in the strong operator topology: $Q_iu\to Qu$ in $H$ for every $u\in H$.
--
--   Then every $Q_iT$ and $QT$ is nuclear, and
--
--   $$
--   \lim_{i}\ \|Q_iT-QT\|_{\mathrm{Tr}}=0,\qquad \lim_{i}\ \operatorname{Trace}(Q_iT)=\operatorname{Trace}(QT).
--   $$
--
--   For sequences the bound in 1. is automatic by the uniform boundedness principle; for nets it is a genuine hypothesis. No convergence of the adjoints $Q_i^*$ is needed for multiplication on the left; the companion statement for multiplication on the right, which does need it, is `MasulloRepair.nuclear_comp_right_adjoint_sot_tendsto_traceNorm`.
--
--   The statement is reusable wherever a trace is computed as a limit of traces of truncations $Q_iT$ with $Q_i$ not converging to the identity, which is the situation of the spectral and geometric truncations in §10.4 and §11.2 of the manuscript.
--
--   **Formalization Note** Nuclearity, the trace $\operatorname{Trace}$ and the trace norm $\|A\|_{\mathrm{Tr}}=\operatorname{Trace}|A|$ are the platform definitions `IsNuclearOperator`, `operatorTrace` and `traceNorm` of `Def_MasulloGRH_HilbertNuclear` (Definition C.3.4.2 of the manuscript). The limit is taken along an arbitrary filter `l`, and the trace-norm convergence is stated as $\|Q_iT-QT\|_{\mathrm{Tr}}\to0$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Lemma C.3.4.4(5), p. 698, and Corollary C.3.5.5, p. 702 (generalized); used in Theorem 11.2.1.2, p. 488

import Definitions.Def_MasulloGRH_HilbertNuclear

set_option autoImplicit false

open Filter Topology MasulloGRH

theorem MasulloRepair.nuclear_comp_left_sot_tendsto_traceNorm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : IsNuclearOperator T)
    {ι : Type*} (l : Filter ι) (Q : ι → H →L[ℂ] H) (Q₀ : H →L[ℂ] H) (C : ℝ)
    (hbd : ∀ᶠ i in l, ‖Q i‖ ≤ C)
    (hQ : ∀ u : H, Tendsto (fun i => Q i u) l (𝓝 (Q₀ u))) :
    (∀ i, IsNuclearOperator (Q i ∘L T)) ∧ IsNuclearOperator (Q₀ ∘L T) ∧
    Tendsto (fun i => traceNorm (Q i ∘L T - Q₀ ∘L T)) l (𝓝 0) ∧
    Tendsto (fun i => operatorTrace (Q i ∘L T)) l (𝓝 (operatorTrace (Q₀ ∘L T))) := by sorry
