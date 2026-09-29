-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_godementWhittaker2_symplecticFourier_swap_eq_godementWhittaker2_of_weight
-- name    : LanglandsTunnell.CubicInduction.godementWhittaker2_symplecticFourier_swap_eq_godementWhittaker2_of_weight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/161d81f9-f3e7-5768-877b-e079083ef5fc
-- title:
--   Symplectic Fourier swap for Godement–Whittaker integrals on GL₂(ℚₚ)
-- statement:
--   Let $p$ be a height-one prime of $\mathcal{O}_{\mathbb Q}$ and write $F = \mathbb{Q}_p$ for the completion `p.adicCompletion ℚ`, equipped with its Borel $\sigma$-algebra and with the measure `selfDualHaarAt ℚ p`, the additive Haar measure giving the valuation ring mass $(\#\mathcal O/p)^{-\ell/2}$ where $\ell$ is the level of the standard local additive character $\psi =$ `psiLocal ℚ p` (the restriction of the standard adelic character of $\mathbb Q$ along the embedding of $F$ at $p$). Let $\chi_0,\chi_1 \colon F^\times \to \mathbb C^\times$ be monoid homomorphisms (indexed as $\chi_i$, $i \in \{0,1\}$), each assumed locally constant but with no unitarity or chamber condition; let $\Phi \colon F^2 \to \mathbb C$ be locally constant with compact support; let $c \colon \mathbb{Z}^{\mathrm{Multiplicative}} \cup \{0\} \to \mathbb C$ be an arbitrary function on the value group, subject to no hypothesis; and let $g \in GL_2(F)$ with rows $e_1 g, e_2 g$. Write $|x| =$ `modulus x` for the module of $x$ (the distributive Haar character of multiplication by $x$, and $0$ at $x=0$), $d^\times t$ for the pushforward to $F^\times$ of the measure $|x|^{-1}$ times additive Haar restricted to $F \setminus \{0\}$, and $$\Phi^\sharp(w) = \int_{F^2} \Phi(u)\,\psi(u_1 w_0 - u_0 w_1)\,du$$ for the symplectic Fourier transform, the inner integral being against the product of two copies of the self-dual measure. The assertion is the identity $$\chi_1(\det g)\,|\det g|^{1/2} \int_{F^\times} c\bigl(v(t)\,v(\det g)\bigr) \Bigl(\int_F \Phi^\sharp\bigl(t\,e_1 g + y\,e_2 g\bigr)\psi(t^{-1}y)\,dy\Bigr) \chi_1(t)\chi_0(t)^{-1}\,d^\times t$$ $$= \chi_0(\det g)\,|\det g|^{1/2} \int_{F^\times} c\bigl(v(t)^{-1}\bigr) \Bigl(\int_F \Phi\bigl(t\,e_1 g + y\,e_2 g\bigr)\psi(t^{-1}y)\,dy\Bigr) \chi_0(t)\chi_1(t)^{-1}\,d^\times t,$$ where $v$ denotes the valuation of $F$ with values in $\mathbb{Z}^{\mathrm{Multiplicative}} \cup \{0\}$, and the half-power of the module is taken as a complex power of the real number $|\det g|$.
--
--   With $c \equiv 1$ this is the interchange $\mathcal W^{(\chi_1,\chi_0)}_{\Phi^\sharp} = \mathcal W^{(\chi_0,\chi_1)}_{\Phi}$ of the Jacquet–Langlands integral model of the Whittaker functions of the principal series $I(\chi_0,\chi_1)$ of $GL_2(\mathbb Q_p)$, here in a form carrying an arbitrary weight $c$ on the value group, so that windowed (truncated) variants are covered; note that a window in $v(t)v(\det g)$ on the $\Phi^\sharp$ side corresponds to a window in $v(t)^{-1}$ on the $\Phi$ side. It feeds the local functional equations for the $GL_2 \times GL_2$ Rankin–Selberg integrals attached to principal series and to cuspidal data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_godementWhittaker2_symplecticFourier_swap_eq_godementWhittaker2_of_weight.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction
open NumberField.AdelicLevel (diagOne)

theorem LanglandsTunnell.CubicInduction.godementWhittaker2_symplecticFourier_swap_eq_godementWhittaker2_of_weight
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i))
    (Φ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (c : WithZero (Multiplicative ℤ) → ℂ)
    (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    letI := localBorel ℚ p
    ((χ 1 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
          ∫ t : (p.adicCompletion ℚ)ˣ,
            c (Valued.v (t : p.adicCompletion ℚ) * Valued.v ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) *
              (∫ y : p.adicCompletion ℚ, (fun v : Fin 2 → p.adicCompletion ℚ =>
              ∫ u : Fin 2 → p.adicCompletion ℚ, Φ u * NumberField.StandardAddChar.psiLocal ℚ p (u 1 * v 0 - u 0 * v 1)
                ∂(Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p)) (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j + y * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) *
                  NumberField.StandardAddChar.psiLocal ℚ p ((t : p.adicCompletion ℚ)⁻¹ * y) ∂(selfDualHaarAt ℚ p)) *
              ((χ 1 t : ℂˣ) : ℂ) * (((χ 0 t : ℂˣ) : ℂ))⁻¹ ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) =
      ((χ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
          ∫ t : (p.adicCompletion ℚ)ˣ,
            c (Valued.v (t : p.adicCompletion ℚ))⁻¹ *
              (∫ y : p.adicCompletion ℚ, Φ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j + y * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) *
                  NumberField.StandardAddChar.psiLocal ℚ p ((t : p.adicCompletion ℚ)⁻¹ * y) ∂(selfDualHaarAt ℚ p)) *
              ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by sorry
