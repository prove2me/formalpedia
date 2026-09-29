-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_mul_mul_rs22Kernel_centralScalar_mul_eq_and_mul_godementSection_eq_integral
-- name    : LanglandsTunnell.RankinSelberg.mul_mul_rs22Kernel_centralScalar_mul_eq_and_mul_godementSection_eq_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/ffe39f84-ad4b-53a5-b1dd-8d17cb257c01
-- title:
--   Central unfolding of the Rankin–Selberg Godement section
-- statement:
--   Let $F$ be a number field, let the idèle group $\mathbb{A}_F^\times$ carry a measurable space structure and let $\nu_0$ be a measure on it. Let $\mu,\nu,\omega,\omega' : \mathbb{A}_F^\times \to \mathbb{C}^\times$ be characters (monoid homomorphisms) with $\omega\omega'\mu\nu = 1$, let $\Phi : \mathbb{A}_F^2 \to \mathbb{C}$, let $s \in \mathbb{C}$, and let $W, W' : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ satisfy $W(zg)W'(zg) = \omega(z)\omega'(z)\,W(g)W'(g)$ for every idèle $z$, where $z$ acts through the central scalar matrix $\mathrm{diag}(z,z)$, and every $g$. Fix $g \in \mathrm{GL}_2(\mathbb{A}_F)$. Write $\alpha$ for the module character `moduleChar F` attached to `distribHaarChar` on $\mathbb{A}_F$ (real-valued and positive), $\alpha(x)^w$ for the corresponding complex power, and $\|t\|$ for `ideleNorm F t`. Then two assertions hold. First, for every idèle $t$, $$W(\mathrm{diag}(t,t)g)\,W'(\mathrm{diag}(t,t)g)\cdot \mu(\det(\mathrm{diag}(t,t)g))\,\alpha(\det(\mathrm{diag}(t,t)g))^{s+1/2}\,\Phi\big((g_{1j})_j\big)$$ — the last factor being $\Phi$ of the bottom row of $\mathrm{diag}(t,t)g$ scaled by $1$ — equals $W(g)W'(g)\cdot\big(\mu(\det g)\,\alpha(\det g)^{s+1/2}\big)\cdot\big(\Phi(t\cdot(g_{1j})_j)\,(\mu\nu^{-1})(t)\,\|t\|^{2s+1}\big)$. Second, $W(g)W'(g)$ times the Godement section $\mu(\det g)\,\alpha(\det g)^{s+1/2}\int_{\mathbb{A}_F^\times}\Phi(t\cdot(g_{1j})_j)(\mu\nu^{-1})(t)\|t\|^{2s+1}\,d\nu_0(t)$ equals the Bochner integral over $t \in \mathbb{A}_F^\times$ of the left-hand side of the first identity. No integrability hypothesis is imposed; both sides are Bochner integrals in the Mathlib convention.
--
--   This is the bookkeeping step over the centre in the Godement–Jacquet unfolding of the global $\mathrm{GL}_2\times\mathrm{GL}_2$ Rankin–Selberg integral: it converts the integral over the idèles of the translated kernel into the product of $W W'$ with the Godement section, whose inner integral is a Tate zeta integral for the character $\mu\nu^{-1}$ at $2s+1$. It is used in the construction of the global Rankin–Selberg integral as an integral over the quotient by the rational centre and unipotent subgroup against a Whittaker integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_mul_mul_rs22Kernel_centralScalar_mul_eq_and_mul_godementSection_eq_integral.lean

import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicFourier IsDedekindDomain NumberField.TateGlobal
open AutomorphicForm LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.mul_mul_rs22Kernel_centralScalar_mul_eq_and_mul_godementSection_eq_integral
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ)
    (μ ν ω ω' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hωμν : ω * ω' * μ * ν = 1)
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ)
    (W W' : AdelicGL2 (𝓞 F) F → ℂ)
    (hZ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      W (centralScalar (𝓞 F) F z * g) * W' (centralScalar (𝓞 F) F z * g) =
        ((ω z : ℂˣ) : ℂ) * ((ω' z : ℂˣ) : ℂ) * (W g * W' g))
    (g : AdelicGL2 (𝓞 F) F) :
    (∀ t : (AdeleRing (𝓞 F) F)ˣ,
      W (centralScalar (𝓞 F) F t * g) * W' (centralScalar (𝓞 F) F t * g) *
          rs22Kernel F μ (moduleChar F) (moduleChar_pos F) Φ s (centralScalar (𝓞 F) F t * g) =
        W g * W' g *
          (((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((cpowChar (moduleChar F) (moduleChar_pos F) (s + 1 / 2) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) *
          (Φ (bottomRowVec F g t) * (((μ * ν⁻¹) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1))) ∧
    W g * W' g * godementSection F ν₀ μ ν (moduleChar F) (moduleChar_pos F) Φ s g =
      ∫ t : (AdeleRing (𝓞 F) F)ˣ,
        W (centralScalar (𝓞 F) F t * g) * W' (centralScalar (𝓞 F) F t * g) *
          rs22Kernel F μ (moduleChar F) (moduleChar_pos F) Φ s (centralScalar (𝓞 F) F t * g) ∂ν₀ := by sorry
