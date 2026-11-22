-- Prove2me | Theorems.Thm_KroneckerWeyl_tendsto_average_torusFlow_closure
-- name    : KroneckerWeyl.tendsto_average_torusFlow_closure
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:31:30.416263+00:00
-- url     : https://prove2.me/theorems/9ecd2b33-c32b-40b7-895a-06cb2e6c303e
-- title:
--   Theorem B.5.2.1(2) (Kronecker–Weyl) — time averages of a continuous function along a linear flow on $\mathbb T^N$ converge to its Haar integral over the orbit closure $G$
-- statement:
--   **Theorem B.5.2.1(2) (Kronecker–Weyl), continuous functions, arbitrary frequencies.** Let $N\ge0$, $\mathbb T=\mathbb R/\mathbb Z$, let $\tau=(\tau_1,\dots,\tau_N)\in\mathbb R^N$ be an arbitrary vector and $\overline\gamma(t)=(t\tau_1,\dots,t\tau_N)\bmod\mathbb Z^N$ the continuous one-parameter subgroup of $\mathbb T^N$ it generates. Let $G=\overline{\overline\gamma(\mathbb R)}$ be the closure of its image, a compact subgroup of $\mathbb T^N$ (a subtorus, by part (1) of the theorem), and let $\mu_G$ be the Haar measure of total mass $1$ on $G$. Then for every continuous function $u\colon G\to\mathbb C$,
--   $$\lim_{T\to+\infty}\frac1{2T}\int_{-T}^{T}u(\overline\gamma(t))\,dt=\lim_{T\to+\infty}\frac1T\int_0^Tu(\overline\gamma(t))\,dt=\int_Gu(\xi)\,d\mu_G(\xi).$$
--
--   This is equation (B.5.2.1) of the source for continuous $u$ and with no independence assumption on the coordinates of $\tau$; it is the case which the source's proof establishes directly (by Stone–Weierstrass and orthogonality of characters, following Humphreys) and from which the Riemann-integrable case is deduced. The source applies it to $\tau_v=\log(q_v)/2\pi$, $v\in S$ a finite set of finite places, whose coordinates can be $\mathbb Q$-linearly dependent (proof of Proposition B.5.3.3).
--
--   **Formalization Note.** The index set $\{1,\dots,N\}$ is an arbitrary finite type `ι` (so $N=0$ is allowed). $\mathbb T$ is Mathlib's `UnitAddCircle = AddCircle (1 : ℝ)`, the coercion `ℝ → UnitAddCircle` is the quotient map $\mathbb R\to\mathbb R/\mathbb Z$, and $\mathbb T^N$ is `ι → UnitAddCircle` (Mathlib's `UnitAddTorus ι`) with the product topology; $\overline\gamma_\tau(t)$ is written inline as `fun k => ((t * τ k : ℝ) : UnitAddCircle)`. The orbit closure is an additive subgroup `G` of `UnitAddTorus ι` with the hypothesis `hG` that its underlying set is the closure of the range of $\overline\gamma$; $\mu_G$ is any measure `μ` on the subtype `G` with `μ.IsAddHaarMeasure` and `IsProbabilityMeasure μ` (it is unique). The function $u$ is taken continuous on the ambient torus, `u : C(UnitAddTorus ι, ℂ)`, and only its restriction to $G$ enters the statement; since $G$ is closed, every continuous function on $G$ is such a restriction (Tietze), so this is the statement for all continuous $u\colon G\to\mathbb C$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 627, Theorem B.5.2.1(2) (Kronecker-Weyl), eq. (B.5.2.1), case of continuous u; classical reference: B. Hasselblatt and A. Katok, A First Course in Dynamics. With a Panorama of Recent Developments, Cambridge University Press, 2003, Part 1, Theorem 4.1.15 and §4.1.6 (of which the source's theorem is the multi-dimensional version); P. Humphreys, The Summatory Function of Liouville's Function and Pólya's Conjecture, BPh thesis, Australian National University, 2010, §4.3, proof of Lemma 4.3 (general case, as cited by the source)

import Mathlib

open MeasureTheory Filter Topology

set_option autoImplicit false

namespace KroneckerWeyl

theorem tendsto_average_torusFlow_closure {ι : Type*} [Finite ι] (τ : ι → ℝ)
    (G : AddSubgroup (UnitAddTorus ι))
    (hG : (G : Set (UnitAddTorus ι)) =
      closure (Set.range fun t : ℝ => fun k : ι => ((t * τ k : ℝ) : UnitAddCircle)))
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : C(UnitAddTorus ι, ℂ)) :
    Tendsto (fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..T, u fun k => ((t * τ k : ℝ) : UnitAddCircle))
        atTop (𝓝 (∫ g : G, u (g : UnitAddTorus ι) ∂μ)) ∧
      Tendsto
        (fun T : ℝ => (2 * T)⁻¹ • ∫ t in (-T)..T, u fun k => ((t * τ k : ℝ) : UnitAddCircle))
        atTop (𝓝 (∫ g : G, u (g : UnitAddTorus ι) ∂μ)) := by sorry

end KroneckerWeyl
