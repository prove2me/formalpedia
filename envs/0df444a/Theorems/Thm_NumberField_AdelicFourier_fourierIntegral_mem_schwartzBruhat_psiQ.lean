-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_psiQ
-- name    : NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat_psiQ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/70811c6d-b0c0-5f48-a6ed-c316871450e5
-- title:
--   Schwartz–Bruhat stability of the ψ_ℚ-Fourier transform
-- statement:
--   Work on the adele ring $\mathbb{A}_{\mathbb{Q}} =$ `AdeleRing (𝓞 ℚ) ℚ`, equipped with a measurable space structure which is the Borel structure of its topology, and let $\mu$ be a measure on $\mathbb{A}_{\mathbb{Q}}$ which is an additive Haar measure. Let $f : \mathbb{A}_{\mathbb{Q}} \to \mathbb{C}$ belong to `schwartzBruhat ℚ`, the $\mathbb{C}$-submodule of functions on $\mathbb{A}_{\mathbb{Q}}$ spanned by the pure tensors, namely the functions of the form $x \mapsto g(\iota(x_\infty))\, h(x_{\mathrm{fin}})$ with $g$ a Schwartz function on the mixed space of $\mathbb{Q}$, $\iota$ the ring isomorphism from the infinite adeles onto that mixed space, and $h$ a locally constant function of compact support on the finite adele ring. The conclusion is that the function $$w \mapsto \int_{\mathbb{A}_{\mathbb{Q}}} \psi_{\mathbb{Q}}(-(v w))\, f(v)\, d\mu(v)$$ again lies in `schwartzBruhat ℚ`, where $\psi_{\mathbb{Q}} =$ [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615) is the additive character of $\mathbb{A}_{\mathbb{Q}}$ sending $x$ to $\psi_{\mathrm{arch}}(x_\infty)\,\psi_{\mathrm{fin}}(x_{\mathrm{fin}})$, the first factor being the finite product over the infinite places of the local characters `psiArchPlace`, the second the finite product over the height-one primes of $\mathcal{O}_{\mathbb{Q}}$ of the local characters `psiV`.
--
--   This is the adelic Fourier inversion input for $\mathbb{Q}$ in the style of Tate's thesis: the Schwartz–Bruhat space of $\mathbb{A}_{\mathbb{Q}}$ is preserved by the Fourier transform taken with respect to the standard global additive character and any Haar measure. It is used in the cubic-induction step of the Langlands–Tunnell argument, where an orthogonality computation with Whittaker functions requires the transform of a Schwartz–Bruhat function to be admissible as a test function again.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_psiQ.lean

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier

theorem NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat_psiQ [MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)] [BorelSpace (AdeleRing (𝓞 ℚ) ℚ)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 ℚ) ℚ)) [μ.IsAddHaarMeasure] {f : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ schwartzBruhat ℚ) :
    fourierIntegral NumberField.StandardAddChar.psiQ μ f ∈ schwartzBruhat ℚ := by sorry
