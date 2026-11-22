-- Prove2me | Theorems.Thm_LCAGroup_convolution_L2_zeroAtInfty
-- name    : LCAGroup.convolution_L2_zeroAtInfty
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:25.267611+00:00
-- url     : https://prove2.me/theorems/89c88251-a13e-425c-907f-bc179559cc22
-- title:
--   Lemma D.1.1.2(3) — for $f_1,f_2\in L^2(G)$ the convolution $f_1*f_2$ is defined everywhere, lies in $C_0(G)$, and $\|f_1*f_2\|_u\le\|f_1\|_2\,\|f_2\|_2$
-- statement:
--   **Convolution of two square-integrable functions on a locally compact abelian group** (Lemma D.1.1.2(3) of the source).
--
--   Let $G$ be a Hausdorff locally compact abelian group with a Haar measure $\mu_G$, and let $f_1,f_2\in L^2(G,\mu_G)$. Their convolution is
--   $$(f_1*f_2)(x)=\int_G f_1(g)\,f_2(g^{-1}x)\,d\mu_G(g)\qquad\text{(D.1.1.5)}.$$
--   Then:
--
--   1. for **every** $x\in G$ the function $g\mapsto f_1(g)\,f_2(g^{-1}x)$ is $\mu_G$-integrable, so $(f_1*f_2)(x)$ is a well-defined complex number for all $x$;
--   2. $f_1*f_2$ is continuous and vanishes at infinity, i.e. $f_1*f_2\in C_0(G)$;
--   3. its sup-norm satisfies
--   $$\|f_1*f_2\|_u\le\|f_1\|_2\cdot\|f_2\|_2\qquad\text{(D.1.1.8)}.$$
--
--   The source records this in Lemma D.1.1.2 among the basic properties of the Fourier transform on $G$, collected for later reference. Functions of the form $f_1*f_2$ with $f_i\in L^2$ are the standard supply of continuous functions vanishing at infinity in Plancherel and Fourier inversion arguments.
--
--   **Formalization Note.** `f g : G → ℂ` are functions with `MemLp f 2 μ`, `MemLp g 2 μ` (any representatives of the two classes); the convolution is the platform definition `RiemannMasullo.lcaConvolution μ f g x = ∫ y, f y * g (y⁻¹ * x) ∂μ`, a Bochner integral whose integrand is asserted to be integrable for every `x` (part 1). Parts 2–3 are expressed by the existence of an element `F` of Mathlib's `C₀(G, ℂ)` (continuous functions vanishing at infinity, with the sup-norm) that agrees with the convolution at every point; `(eLpNorm f 2 μ).toReal` is $\|f\|_2$. Haar measures are regular (`IsHaarMeasure` together with `Measure.Regular`), as in the cited reference; regularity is automatic when $G$ is second countable.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 746–747, eq. (D.1.1.5) and Lemma D.1.1.2(3), eq. (D.1.1.8); classical reference: W. Rudin, Fourier Analysis on Groups, Wiley-Interscience, 1962, 1.1.6(d) (with Hölder's inequality for the norm bound)

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution

open MeasureTheory Topology
open scoped ZeroAtInfty

set_option autoImplicit false

namespace LCAGroup

theorem convolution_L2_zeroAtInfty
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (f g : G → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∀ x : G, Integrable (fun y : G => f y * g (y⁻¹ * x)) μ) ∧
    ∃ F : C₀(G, ℂ), (∀ x : G, F x = RiemannMasullo.lcaConvolution μ f g x) ∧
      ‖F‖ ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by sorry

end LCAGroup
