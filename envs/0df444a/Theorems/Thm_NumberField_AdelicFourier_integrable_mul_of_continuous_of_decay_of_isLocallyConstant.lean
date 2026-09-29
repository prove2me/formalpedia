-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_integrable_mul_of_continuous_of_decay_of_isLocallyConstant
-- name    : NumberField.AdelicFourier.integrable_mul_of_continuous_of_decay_of_isLocallyConstant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/a280a1f9-cef6-5e68-b47d-592ca1410bcd
-- title:
--   Integrability of a decaying archimedean times locally constant finite factor
-- statement:
--   Let $F$ be a number field, and equip the adele ring $\mathbb{A}_F$ of $F$ with a measurable structure that is the Borel structure of its topology, together with an additive Haar measure $\mu$. Let $G \colon F_\infty \to \mathbb{C}$ be a continuous function on the mixed space $\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ attached to $F$, let $k$ be a natural number strictly larger than $\dim_{\mathbb{R}}$ of that mixed space, and let $C$ be a real number such that $(1 + \lVert y \rVert)^k \lVert G(y)\rVert \le C$ for every $y$ in the mixed space, so that $G$ decays faster than any reciprocal power up to order $k$. Let $H \colon \mathbb{A}_F^{\mathrm{f}} \to \mathbb{C}$ be a function on the finite adele ring of $\mathcal{O}_F$ in $F$ which is locally constant and has compact support. Then the function on $\mathbb{A}_F$ sending $x$ to $G(\iota(x_\infty)) \cdot H(x_{\mathrm{f}})$, where $x_\infty$ and $x_{\mathrm{f}}$ are the infinite and finite components of $x$ and $\iota$ is the ring isomorphism from the infinite adele ring to the mixed space, is integrable with respect to $\mu$.
--
--   This is the basic integrability criterion for product functions on the adeles of Schwartz–Bruhat type, with the archimedean factor required only to satisfy a polynomial decay bound of order exceeding the real dimension of $F_\infty$ rather than to be Schwartz. It serves as a dominating-function supply for integrability and dominated-convergence arguments in the adelic Fourier analysis used in the construction of cubic inductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_integrable_mul_of_continuous_of_decay_of_isLocallyConstant.lean

import Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

theorem NumberField.AdelicFourier.integrable_mul_of_continuous_of_decay_of_isLocallyConstant
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (G : mixedEmbedding.mixedSpace F → ℂ) (hG : Continuous G)
    (k : ℕ) (hk : Module.finrank ℝ (mixedEmbedding.mixedSpace F) < k)
    (C : ℝ) (hdecay : ∀ y : mixedEmbedding.mixedSpace F, (1 + ‖y‖) ^ k * ‖G y‖ ≤ C)
    (H : FiniteAdeleRing (𝓞 F) F → ℂ) (hH : IsLocallyConstant H) (hHc : HasCompactSupport H) :
    Integrable (fun x : AdeleRing (𝓞 F) F => G (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * H x.2) μ := by sorry
