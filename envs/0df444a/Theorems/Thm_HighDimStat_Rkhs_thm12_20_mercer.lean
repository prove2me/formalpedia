-- Prove2me | Theorems.Thm_HighDimStat_Rkhs_thm12_20_mercer
-- name    : HighDimStat.Rkhs.thm12_20_mercer
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:28:30.044956+00:00
-- url     : https://prove2.me/theorems/f71ce008-6981-415c-ad48-fbd4a215e343
-- title:
--   Mercer's theorem — eigenexpansion of a continuous PSD kernel (Theorem 12.20)
-- statement:
--   **Theorem 12.20 (Mercer's theorem).** A deeper structural result the RKHS correspondence
--   builds toward: under compactness and continuity, a PSD kernel admits an explicit
--   eigenfunction expansion, generalizing the spectral decomposition of a PSD matrix.
--
--   Suppose $X$ is a compact metric space, $P$ a finite measure on $X$, the kernel $K$ is
--   continuous and positive semidefinite, and satisfies the Hilbert-Schmidt condition (12.11b),
--   $\int_{X\times X}K^2(x,z)\,dP(x)\,dP(z)<\infty$, so that the integral operator
--   $T_K(f)(x):=\int_X K(x,z)f(z)\,dP(z)$ (Eq. 12.11a) is a bounded linear operator on
--   $L^2(X;P)$. Then there is a countable index set $\iota$, an orthonormal basis
--   $(\varphi_j)_{j\in\iota}$ of $L^2(X;P)$, and non-negative eigenvalues $(\mu_j)_{j\in\iota}$
--   with
--
--   $$
--   T_K(\varphi_j) = \mu_j\varphi_j \qquad \text{for every } j,
--   $$
--
--   and the kernel has the expansion
--
--   $$
--   K(x,z) = \sum_{j\in\iota} \mu_j\varphi_j(x)\varphi_j(z),
--   $$
--
--   where the series converges both **absolutely** (for every fixed $(x,z)$) and, along every
--   enumeration of $\iota$ by $\mathbb N$, **uniformly** on $X\times X$.
--
--   **Formalization Note** The integral operator $T_K$ is represented as an abstract linear
--   map on `Lp ℝ 2 P` tied to the defining integral formula (12.11a) via the hypothesis
--   `hTK`, rather than constructed as a `def` — constructing it as a genuine well-defined
--   linear operator on `Lp` requires real analytic proof work (integrability,
--   a.e.-strong-measurability of the integrand) that belongs in the eventual proof, not in a
--   sorry-free definitions file. The orthonormal basis is Mathlib's `HilbertBasis ι ℝ (Lp ℝ 2
--   P)`, which already packages orthonormality together with completeness (spanning) as a
--   Hilbert-space basis, matching "form an orthonormal basis of $L^2(X;P)$" directly.
--   **Revision 1**: the index type $\iota$ is existentially quantified (`∃ (ι : Type) (_ :
--   Countable ι), ...`) rather than fixed to $\mathbb N$ as in the original draft. Fixing it to
--   $\mathbb N$ forced `HilbertBasis ℕ ℝ (Lp ℝ 2 P)`, i.e. `Lp ℝ 2 P ≃ ℓ²(ℕ,ℝ)`, which is false
--   whenever $L^2(X;P)$ is finite-dimensional — any finite $X$, e.g. Example 12.18/12.21's
--   discrete case, which the book's own text treats as an instance of this theorem — making the
--   original statement mathematically false there. Pointwise evaluation $\varphi_j(x)$ uses the
--   canonical a.e.-defined `Lp` coercion to functions. Absolute convergence is stated as `HasSum`
--   of the real-valued series over $\iota$ (for $\mathbb R$-valued series, unconditional/`HasSum`
--   convergence is equivalent to absolute convergence, unlike in general infinite-dimensional
--   Banach spaces); uniform convergence is stated separately via `TendstoUniformly`, per this
--   chapter's named pitfall that Mercer's conclusion is not merely pointwise or $L^2$
--   convergence, and — since "partial sum" needs an enumeration order when $\iota\ne\mathbb N$ —
--   is quantified over every bijection `e : ℕ ≃ ι` (vacuously true when $\iota$ is finite, since
--   no such bijection exists there, correctly imposing no constraint in that case; a genuine,
--   order-independent uniform-convergence claim when $\iota$ is countably infinite, which the
--   non-negativity of the diagonal terms $\mu_j\varphi_j(x)^2$ at $x=z$ makes provable for any
--   enumeration, not just a chosen canonical one).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 395 (PDF p. 415), Theorem 12.20, Eqs. (12.11a)-(12.11b), (12.13a)-(12.13b)

import Mathlib
import Definitions.Def_HighDimStat_Rkhs_Core

namespace HighDimStat.Rkhs

open scoped RealInnerProductSpace
open MeasureTheory

/-- Theorem 12.20 (Mercer's theorem, p. 395): suppose `X` is a compact metric space, `P` is a
finite measure on `X`, the kernel `K` is continuous, positive semidefinite, and satisfies the
Hilbert-Schmidt condition (12.11b) (the associated integral operator `TK` of (12.11a) is
represented here abstractly by a linear map on `L²(X;P)` tied to the integral formula via
`hTK`). Then there is a countable orthonormal basis `(φⱼ)_{j∈ι}` of `L²(X;P)` and non-negative
eigenvalues `(μⱼ)` with `TK(φⱼ) = μⱼφⱼ` for every `j` (Eq. 12.13a), and the kernel has the
expansion `K(x,z) = Σⱼ μⱼφⱼ(x)φⱼ(z)`, with the series converging both absolutely (pointwise
`HasSum`, for real-valued series equivalent to unconditional/absolute convergence) and, along
every enumeration of `ι` by `ℕ` (when one exists — vacuous when `ι` is finite, e.g. when
`L²(X;P)` itself is finite-dimensional, per Example 12.21), uniformly on `X × X` (Eq. 12.13b).
The index type `ι` is existentially quantified (Revision 1) rather than fixed to `ℕ`: pinning it
to `ℕ` would force `L²(X;P) ≃ ℓ²(ℕ,ℝ)`, which is false whenever `L²(X;P)` is finite-dimensional
(any finite `X`, e.g. Example 12.18/12.21's discrete case), making the original statement
mathematically false for a case the book's own text treats as an instance of this theorem. -/
theorem thm12_20_mercer {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (P : Measure X) [IsFiniteMeasure P]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) (hKpsd : IsPSDKernel K)
    (hHS : Integrable (fun p : X × X => (K p.1 p.2) ^ 2) (P.prod P))
    (TK : Lp ℝ 2 P →ₗ[ℝ] Lp ℝ 2 P)
    (hTK : ∀ f : Lp ℝ 2 P, (TK f : X → ℝ) =ᵐ[P] fun x => ∫ z, K x z * (f z) ∂P) :
    ∃ (ι : Type) (_ : Countable ι) (φ : HilbertBasis ι ℝ (Lp ℝ 2 P)) (μ : ι → ℝ),
      (∀ j, 0 ≤ μ j) ∧
      (∀ j, TK (φ j) = μ j • (φ j : Lp ℝ 2 P)) ∧
      (∀ x z, HasSum (fun j => μ j * (φ j : X → ℝ) x * (φ j : X → ℝ) z) (K x z)) ∧
      (∀ e : ℕ ≃ ι, TendstoUniformly (fun n : ℕ => fun p : X × X =>
          ∑ k ∈ Finset.range n, μ (e k) * (φ (e k) : X → ℝ) p.1 * (φ (e k) : X → ℝ) p.2)
        (Function.uncurry K) Filter.atTop) := by sorry

end HighDimStat.Rkhs
