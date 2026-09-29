-- Prove2me | Theorems.Thm_LanglandsTunnell_HeckeTate_finprod_euler_comp_X_pow_inertiaDeg_eq_inducedEulerPoly_comp
-- name    : LanglandsTunnell.HeckeTate.finprod_euler_comp_X_pow_inertiaDeg_eq_inducedEulerPoly_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/1743d69d-54fd-54bd-ba7d-23199938545b
-- title:
--   Euler factors above p of a norm-twisted idele character
-- statement:
--   Let $K$ be a number field whose ring of integers is given as an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, let $\mu\colon (\mathbb{A}_K^\times) \to \mathbb{C}^\times$ and $\tau\colon (\mathbb{A}_{\mathbb{Q}}^\times)\to\mathbb{C}^\times$ be group homomorphisms of the idele groups, let $uR, aR$ be functions assigning to each real place of $K$ an element of $\mathbb{C}$ and of $\mathbb{Z}/2$, and $uC, kC$ functions assigning to each complex place of $K$ an element of $\mathbb{C}$ and of $\mathbb{Z}$, and let $p$ be a finite prime of $\mathbb{Q}$ at which $\tau$ is unramified, i.e. the local component of $\tau$ at $p$ is trivial on those units of the completion whose inverse is again integral. Put $\chi=\mu\cdot(\tau\circ N)$, where $N$ is the idelic norm of `genuineBaseChange` from $K$ to $\mathbb{Q}$. Then in $\mathbb{C}[X]$ the finite product, over the primes $\mathfrak{P}$ of $K$ with $\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}=p$, of the Euler polynomial of the L-datum `heckeDatum K \chi uR aR uC kC` at $\mathfrak{P}$ — namely $1-\chi(\varpi_{\mathfrak{P}})X$ if $\chi$ is unramified at $\mathfrak{P}$ and $1$ otherwise, $\varpi_{\mathfrak{P}}$ the uniformiser idele — with $X$ replaced by $X^{f(\mathfrak{P}/p)}$, equals `inducedEulerPoly ℚ (inducedCoeff K μ) p`, the finite product of the factors `inducedFactor ℚ (inducedCoeff K μ) 𝔓` over the same fibre, with $X$ replaced by $\tau(\varpi_p)\,X$; here $f(\mathfrak{P}/p)$ is the inertia degree and `inducedCoeff K μ` sends $\mathfrak{P}$ to $\mu(\varpi_{\mathfrak{P}})$ when $\mu$ is unramified at $\mathfrak{P}$ and to $0$ otherwise. The archimedean data $uR,aR,uC,kC$ enter only through the formation of the L-datum and do not affect its Euler polynomials.
--
--   This is the local-at-$p$ comparison identifying the Euler factors of an idele class character of $K$ twisted by the norm pull-back of a character of $\mathbb{Q}$ with the Euler polynomial induced from $K$ to $\mathbb{Q}$, evaluated after the substitution $X\mapsto\tau(\varpi_p)X$. It feeds the cubic-induction comparisons of completed L-functions used in the converse-theorem step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_HeckeTate_finprod_euler_comp_X_pow_inertiaDeg_eq_inducedEulerPoly_comp.lean

import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicLambda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal
open LanglandsTunnell.Converse LanglandsTunnell.HeckeTate LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda
open LanglandsTunnell.CubicInduction Polynomial

theorem LanglandsTunnell.HeckeTate.finprod_euler_comp_X_pow_inertiaDeg_eq_inducedEulerPoly_comp
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (hτ : IsUnramifiedCharAt τ p) :
    (∏ᶠ 𝔓 ∈ primeFibre ℚ K p,
        ((heckeDatum K (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
            uR aR uC kC).euler 𝔓).comp (X ^ ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal)))
      = (inducedEulerPoly ℚ (inducedCoeff K μ) p).comp (C (eulerCoeff ℚ τ p) * X) := by sorry
