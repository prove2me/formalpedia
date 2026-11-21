-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_convergence_exhaustive_projections
-- name    : MasulloGRH.nuclear_convergence_exhaustive_projections
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-20T22:44:18.585782+00:00
-- url     : https://prove2.me/theorems/f18aeaf1-e8bb-4b8b-993d-c536ea071e03
-- title:
--   Corollary C.3.5.5 — exhaustive filtrations: $P_iT\to T$ and $TP_i\to T$ in trace norm, and $\operatorname{Trace}(P_iT)\to\operatorname{Trace}(T)$
-- statement:
--   An operator $T$ on a Hilbert space $H$ is **nuclear** (trace class) if $Tu=\sum_m\langle u,x_m\rangle y_m$ with $\sum_m\|x_m\|\|y_m\|<\infty$. Its **trace** is $\operatorname{Trace}(T)=\sum_\varphi\langle T\varphi,\varphi\rangle$ over an orthonormal basis, and its **trace norm** is $\|T\|_{\mathrm{Tr}}=\operatorname{Trace}|T|$ with $|T|=(T^*T)^{1/2}$.
--
--   Let $H$ be a separable Hilbert space, $H_1\subset H_2\subset\cdots$ an increasing sequence of closed subspaces with dense union, $P_i$ the orthogonal projector onto $H_i$, and $T$ a nuclear operator on $H$. Then:
--
--   1. $P_iu\to u$ for every $u\in H$;
--   2. $\|P_iT-T\|_{\mathrm{Tr}}\to0$ and $\|TP_i-T\|_{\mathrm{Tr}}\to0$;
--   3. $$\lim_{i\to\infty}\operatorname{Trace}(P_iT)=\lim_{i\to\infty}\operatorname{Trace}(TP_i)=\operatorname{Trace}(T).$$
--
--   The corollary allows the trace of a nuclear operator to be computed as a limit of traces of its compressions to an exhausting sequence of subspaces, which is how the draft evaluates the spectral side of its trace formula.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.3.5, Corollary C.3.5.5 (SOT-exhaustive filtrations and nuclear convergence), eq. (C.3.5.18), p. 702

import Definitions.Def_MasulloGRH_HilbertNuclear

set_option autoImplicit false

namespace MasulloGRH

open MeasureTheory Filter Topology

theorem nuclear_convergence_exhaustive_projections
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (K : ℕ → Submodule ℂ H)
    [∀ i, (K i).HasOrthogonalProjection] (hK : Monotone K) (hcl : ∀ i, IsClosed (K i : Set H))
    (hdense : Dense (⋃ i, (K i : Set H))) (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    (∀ u : H, Tendsto (fun i => (K i).starProjection u) atTop (𝓝 u)) ∧
    Tendsto (fun i => traceNorm ((K i).starProjection ∘L T - T)) atTop (𝓝 0) ∧
    Tendsto (fun i => traceNorm (T ∘L (K i).starProjection - T)) atTop (𝓝 0) ∧
    Tendsto (fun i => operatorTrace ((K i).starProjection ∘L T)) atTop (𝓝 (operatorTrace T)) ∧
    Tendsto (fun i => operatorTrace (T ∘L (K i).starProjection)) atTop (𝓝 (operatorTrace T)) := by sorry

end MasulloGRH
