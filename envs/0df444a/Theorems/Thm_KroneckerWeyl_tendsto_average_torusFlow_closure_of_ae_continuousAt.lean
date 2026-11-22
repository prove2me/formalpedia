-- Prove2me | Theorems.Thm_KroneckerWeyl_tendsto_average_torusFlow_closure_of_ae_continuousAt
-- name    : KroneckerWeyl.tendsto_average_torusFlow_closure_of_ae_continuousAt
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:31:28.750122+00:00
-- url     : https://prove2.me/theorems/43a06758-797c-47e5-944d-d436559b3df3
-- title:
--   Theorem B.5.2.1(2) (Kronecker–Weyl) for Riemann-integrable functions — bounded Borel $u$ on the orbit closure $G$, continuous $\mu_G$-almost everywhere
-- statement:
--   **Theorem B.5.2.1(2) (Kronecker–Weyl) for Riemann-integrable functions.** Let $N\ge0$, $\mathbb T=\mathbb R/\mathbb Z$, let $\tau=(\tau_1,\dots,\tau_N)\in\mathbb R^N$ be an arbitrary vector, $\overline\gamma(t)=(t\tau_1,\dots,t\tau_N)\bmod\mathbb Z^N$ the one-parameter subgroup of $\mathbb T^N$ it generates, $G=\overline{\overline\gamma(\mathbb R)}$ the closure of its image (a subtorus of $\mathbb T^N$) and $\mu_G$ the Haar measure of total mass $1$ on $G$. Let $u\colon G\to\mathbb C$ be a function which is
--
--   1. Borel measurable,
--   2. bounded, and
--   3. continuous at $\mu_G$-almost every point of $G$.
--
--   Then
--   $$\lim_{T\to+\infty}\frac1{2T}\int_{-T}^{T}u(\overline\gamma(t))\,dt=\lim_{T\to+\infty}\frac1T\int_0^Tu(\overline\gamma(t))\,dt=\int_Gu(\xi)\,d\mu_G(\xi).$$
--
--   Conditions 2 and 3 are Lebesgue's criterion for Riemann integrability (transported to $G\simeq\mathbb T^d$, or to the cube $[0,1)^N$ when $G=\mathbb T^N$), so this is equation (B.5.2.1) of the source for Riemann-integrable $u$. The source deduces it from the continuous case by squeezing $u$ between continuous functions (Lemma B.5.2.2) and uses it, through Corollary B.5.2.4, for indicator functions of sets with $\mu_G$-null boundary.
--
--   **Deviation from the source.** The source states (B.5.2.1) "for every Riemann integrable function $u\colon G\to\mathbb C$". As printed this is not well posed: a bounded function that is continuous off a $\mu_G$-null set need not be Borel measurable, and then $t\mapsto u(\overline\gamma(t))$ need not be Lebesgue measurable, since the orbit itself is $\mu_G$-null when $\dim G\ge2$ (take the indicator of the image under $\overline\gamma$ of a non-measurable subset of $[0,1]$). Condition 1 is added to make the time integrals meaningful; with it they are Lebesgue integrals of bounded Borel functions and the statement is the standard extension of weak convergence of the orbit measures to bounded functions continuous almost everywhere.
--
--   **Formalization Note.** The index set $\{1,\dots,N\}$ is an arbitrary finite type `ι` (so $N=0$ is allowed). $\mathbb T$ is Mathlib's `UnitAddCircle = AddCircle (1 : ℝ)`, the coercion `ℝ → UnitAddCircle` is the quotient map $\mathbb R\to\mathbb R/\mathbb Z$, and $\mathbb T^N$ is `ι → UnitAddCircle` (Mathlib's `UnitAddTorus ι`) with the product topology; $\overline\gamma_\tau(t)$ is written inline as `fun k => ((t * τ k : ℝ) : UnitAddCircle)`. The orbit closure is an additive subgroup `G` with hypothesis `hG` (its underlying set is the closure of the range of $\overline\gamma$), and $\mu_G$ is any measure `μ` on the subtype `G` that is an additive Haar measure and a probability measure. The function is given on the ambient torus, `u : UnitAddTorus ι → ℂ`, but all three hypotheses and both sides of the conclusion involve only its restriction `fun g : G => u g` to $G$ (the flow stays in $G$), so the statement is about an arbitrary function on $G$ (extend it by $0$).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 627, Theorem B.5.2.1(2) (Kronecker-Weyl), eq. (B.5.2.1), Riemann-integrable u (with Borel measurability added, see the statement); classical reference: B. Hasselblatt and A. Katok, A First Course in Dynamics. With a Panorama of Recent Developments, Cambridge University Press, 2003, Part 1, Theorem 4.1.15 and §4.1.6 (of which the source's theorem is the multi-dimensional version); P. Humphreys, The Summatory Function of Liouville's Function and Pólya's Conjecture, BPh thesis, Australian National University, 2010, §4.3, proof of Lemma 4.3 (general case, as cited by the source)

import Mathlib

open MeasureTheory Filter Topology

set_option autoImplicit false

namespace KroneckerWeyl

theorem tendsto_average_torusFlow_closure_of_ae_continuousAt {ι : Type*} [Finite ι] (τ : ι → ℝ)
    (G : AddSubgroup (UnitAddTorus ι))
    (hG : (G : Set (UnitAddTorus ι)) =
      closure (Set.range fun t : ℝ => fun k : ι => ((t * τ k : ℝ) : UnitAddCircle)))
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : UnitAddTorus ι → ℂ)
    (hu : Measurable fun g : G => u (g : UnitAddTorus ι))
    (hb : ∃ C : ℝ, ∀ g : G, ‖u (g : UnitAddTorus ι)‖ ≤ C)
    (hc : ∀ᵐ g ∂μ, ContinuousAt (fun g : G => u (g : UnitAddTorus ι)) g) :
    Tendsto (fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..T, u fun k => ((t * τ k : ℝ) : UnitAddCircle))
        atTop (𝓝 (∫ g : G, u (g : UnitAddTorus ι) ∂μ)) ∧
      Tendsto
        (fun T : ℝ => (2 * T)⁻¹ • ∫ t in (-T)..T, u fun k => ((t * τ k : ℝ) : UnitAddCircle))
        atTop (𝓝 (∫ g : G, u (g : UnitAddTorus ι) ∂μ)) := by sorry

end KroneckerWeyl
