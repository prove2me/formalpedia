-- Prove2me | Theorems.Thm_HighDimStat_Rkhs_thm12_20_mercer_v2
-- name    : HighDimStat.Rkhs.thm12_20_mercer_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:20:30.882102+00:00
-- url     : https://prove2.me/theorems/5c710fe3-b632-4235-bddb-f53d00da1646
-- title:
--   Mercer's theorem — eigenexpansion of a continuous PSD kernel (Theorem 12.20), full-support measure
-- statement:
--   **Theorem 12.20 (Mercer's theorem).** A deeper structural result the RKHS correspondence
--   builds toward: under compactness and continuity, a PSD kernel admits an explicit
--   eigenfunction expansion, generalizing the spectral decomposition of a PSD matrix.
--
--   Suppose $X$ is a compact metric space, $\mathbb P$ a finite Borel measure on $X$ with full
--   support (every nonempty open set has positive measure), the kernel $K$ is continuous and
--   positive semidefinite, and satisfies the Hilbert–Schmidt condition (12.11b),
--   $\int_{X\times X}K^2(x,z)\,d\mathbb P(x)\,d\mathbb P(z)<\infty$, so that the integral operator
--   $T_K(f)(x):=\int_X K(x,z)f(z)\,d\mathbb P(z)$ (Eq. 12.11a) is a bounded linear operator on
--   $L^2(X;\mathbb P)$. Then there is a countable index set $\iota$, an orthonormal basis
--   $(\varphi_j)_{j\in\iota}$ of $L^2(X;\mathbb P)$, and non-negative eigenvalues $(\mu_j)_{j\in\iota}$
--   with
--
--   $$
--   T_K(\varphi_j) = \mu_j\varphi_j \qquad \text{for every } j,
--   $$
--
--   such that every eigenfunction with $\mu_j>0$ has a continuous representative $\psi_j$
--   ($\psi_j=\varphi_j$ $\mathbb P$-a.e.), and with these representatives the kernel has the
--   expansion
--
--   $$
--   K(x,z) = \sum_{j\in\iota} \mu_j\psi_j(x)\psi_j(z) \qquad\text{for all } x,z\in X,
--   $$
--
--   where the series converges absolutely (for every fixed $(x,z)$) and, along every
--   enumeration of $\iota$ by $\mathbb N$, uniformly on $X\times X$.
--
--   **Formalization Note.** The retired version (`thm12_20_mercer`) allowed any finite measure,
--   including $\mathbb P=0$, for which $L^2(\mathbb P)=\{0\}$, the Hilbert basis is empty and the
--   expansion sums to $0\ne K$ (accepted disproof); and it asserted the pointwise expansion "for
--   all $x,z$" for the canonical a.e.-defined $L^p$ representatives, whose values on
--   $\mathbb P$-null sets are arbitrary, so the statement could not hold even for a probability
--   measure without full support (with $\mathbb P=\delta_a$ on $X=\{a,b\}$ the representative's value
--   at $b$ is unconstrained; and off the support the kernel is genuinely not determined by the
--   operator). The new statement (i) requires `P.IsOpenPosMeasure` (full support), the standard
--   hypothesis under which Mercer's expansion holds at every point of $X$ — tacit in the source,
--   which treats $\mathbb P$ as the sampling distribution on $X$ — which excludes the zero measure
--   on a nonempty $X$; (ii) states the expansion for continuous representatives $\psi_j$ of the
--   eigenfunctions with positive eigenvalue (as the source does: "the eigenfunctions ... taken
--   continuous"); the terms with $\mu_j=0$ vanish identically, so $\psi_j$ is unconstrained there.
--   As before, $T_K$ is a linear map on `Lp ℝ 2 P` pinned down (uniquely as an $L^2$ element)
--   by the integral formula `hTK`; the index type is existential and countable; absolute
--   convergence is `HasSum` of the real series; uniform convergence is quantified over every
--   bijection `ℕ ≃ ι` (vacuous when $\iota$ is finite). The finite-measure (rather than
--   probability-measure) generality of the retired version is kept.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 395 (PDF p. 415), Theorem 12.20, Eqs. (12.11a)-(12.11b), (12.13a)-(12.13b) — with the tacit full-support hypothesis on P made explicit and the pointwise expansion stated for continuous representatives of the eigenfunctions

import Mathlib
import Definitions.Def_HighDimStat_Rkhs_Core

namespace HighDimStat.Rkhs

open scoped RealInnerProductSpace
open MeasureTheory

/-- Theorem 12.20 (Mercer's theorem, p. 395): suppose `X` is a compact metric space, `P` is a
finite measure on `X` with **full support** (every nonempty open set has positive measure, so
`L²(X;P)` separates points of `X` and `P ≠ 0` when `X ≠ ∅`), the kernel `K` is continuous,
positive semidefinite, and satisfies the Hilbert–Schmidt condition (12.11b) (the associated
integral operator `TK` of (12.11a) is represented by a linear map on `L²(X;P)` pinned down —
uniquely, as an element of `L²` — by the integral formula `hTK`). Then there is a countable
orthonormal basis `(φⱼ)_{j∈ι}` of `L²(X;P)` and non-negative eigenvalues `(μⱼ)` with
`TK(φⱼ) = μⱼφⱼ` for every `j` (Eq. 12.13a); the eigenfunctions with `μⱼ > 0` admit continuous
representatives `ψⱼ` (`ψⱼ = φⱼ` `P`-a.e.), and with these representatives the kernel has the
expansion `K(x,z) = Σⱼ μⱼψⱼ(x)ψⱼ(z)` for **all** `x, z ∈ X`, converging absolutely (pointwise
`HasSum`) and, along every enumeration of `ι` by `ℕ`, uniformly on `X × X` (Eq. 12.13b).

Corrections relative to the retired version: (i) the zero measure was admitted
(`IsFiniteMeasure` alone), for which `L²(P) = {0}`, the basis is empty and the expansion sums
to `0 ≠ K`; the full-support hypothesis `IsOpenPosMeasure P` (the standard hypothesis under
which Mercer's expansion holds at every point of `X`, tacit in the source) excludes it;
(ii) the pointwise expansion was stated for the canonical a.e.-defined `Lp` representatives,
whose values on `P`-null sets are arbitrary, so "for all `x z`" could not hold; it is now
stated for continuous representatives of the eigenfunctions with positive eigenvalue
(the `μⱼ = 0` terms vanish identically), as in the source's statement that the expansion holds
pointwise with continuous eigenfunctions. -/
theorem thm12_20_mercer_v2 {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (P : Measure X) [IsFiniteMeasure P] [P.IsOpenPosMeasure]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) (hKpsd : IsPSDKernel K)
    (hHS : Integrable (fun p : X × X => (K p.1 p.2) ^ 2) (P.prod P))
    (TK : Lp ℝ 2 P →ₗ[ℝ] Lp ℝ 2 P)
    (hTK : ∀ f : Lp ℝ 2 P, (TK f : X → ℝ) =ᵐ[P] fun x => ∫ z, K x z * (f z) ∂P) :
    ∃ (ι : Type) (_ : Countable ι) (φ : HilbertBasis ι ℝ (Lp ℝ 2 P)) (μ : ι → ℝ)
      (ψ : ι → X → ℝ),
      (∀ j, 0 ≤ μ j) ∧
      (∀ j, TK (φ j) = μ j • (φ j : Lp ℝ 2 P)) ∧
      (∀ j, (φ j : X → ℝ) =ᵐ[P] ψ j) ∧
      (∀ j, 0 < μ j → Continuous (ψ j)) ∧
      (∀ x z, HasSum (fun j => μ j * ψ j x * ψ j z) (K x z)) ∧
      (∀ e : ℕ ≃ ι, TendstoUniformly (fun n : ℕ => fun p : X × X =>
          ∑ k ∈ Finset.range n, μ (e k) * ψ (e k) p.1 * ψ (e k) p.2)
        (Function.uncurry K) Filter.atTop) := by sorry

end HighDimStat.Rkhs
