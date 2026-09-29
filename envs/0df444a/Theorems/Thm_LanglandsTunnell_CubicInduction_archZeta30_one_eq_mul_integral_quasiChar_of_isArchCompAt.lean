-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_archZeta30_one_eq_mul_integral_quasiChar_of_isArchCompAt
-- name    : LanglandsTunnell.CubicInduction.archZeta30_one_eq_mul_integral_quasiChar_of_isArchCompAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/a44dad1a-9bb0-5cd6-8a46-7c9d49964ddc
-- title:
--   Archimedean zeta integral Z₀ at 1 as a dy/|y| integral
-- statement:
--   Fix a measurable structure on $(\mathbb{A}_\infty^{\mathbb Q})^\times$ compatible with the topology, and let $\nu^\times$ be a Haar measure on it. Let $\kappa\in\mathbb R$ be such that the pushforward of $\nu^\times$ along $z\mapsto \mathrm{realCoord}(z)$, the real coordinate at the unique infinite place of $\mathbb Q$, equals $\kappa$ times the measure $|y|^{-1}\,dy$ on $\mathbb R$. Let $\sigma:\mathbb{A}_\mathbb{Q}^\times\to\mathbb C^\times$ be a group homomorphism, $t\in\mathbb C$ and $e\in\mathbb Z$ such that at every real infinite place $v$ of $\mathbb Q$ the predicate `IsArchCompAt` holds, i.e. $\sigma$ composed with the local unit inclusion at $v$ sends $x$ to $\|x\|^{\mathrm{mult}(v)\,t}\,(x/\|x\|)^{e}$. Let $E:(\mathbb{A}_\infty^{\mathbb Q})^\times\to\mathbb{A}_\mathbb{Q}^\times$ be a homomorphism with infinite part the identity and finite part $1$. Let $W:\mathrm{GL}_3(\mathbb{A}_\infty^{\mathbb Q})\to\mathbb C$ and $\Phi:\mathbb R\to\mathbb C$ satisfy $W(\iota(\mathrm{diag}(z,1))\cdot 1)=\Phi(\mathrm{realCoord}(z))$ for all units $z$, with $\Phi$ almost everywhere strongly measurable, and let $s\in\mathbb C$. Then $\kappa>0$ and $$\int W(\iota(\mathrm{diag}(a,1)))\,\sigma(E a)\,\|a\|^{s-1}\,d\nu^\times(a)=\kappa\int_{\mathbb R}\Phi(y)\,|y|^{t}\mathrm{sgn}(y)^{e\bmod 2}\,|y|^{s-1}\,|y|^{-1}\,dy,$$ where the sign factor is $1$ when $e$ is even.
--
--   This is the archimedean $\mathrm{GL}_3\times\mathrm{GL}_1$ zeta integral of a Whittaker-type function, evaluated at the identity, rewritten as a Mellin-type integral on the real line against the quasi-character $|y|^{t}\mathrm{sgn}(y)^{e}$. It is the transport step used by the subsequent evaluations of `archZeta30` on explicit harmonic-polynomial-times-Gaussian sections, which produce a product of $\Gamma_{\mathbb R}$-factors and a Mellin transform and thereby feed the converse-theorem input in the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_archZeta30_one_eq_mul_integral_quasiChar_of_isArchCompAt.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse

open scoped Classical in
open LanglandsTunnell LanglandsTunnell.CubicInduction in

theorem LanglandsTunnell.CubicInduction.archZeta30_one_eq_mul_integral_quasiChar_of_isArchCompAt
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (κ : ℝ)
    (hκ : MeasureTheory.Measure.map
        (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
      ENNReal.ofReal κ • (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        fun y => ENNReal.ofReal |y|⁻¹)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (t : ℂ) (e : ℤ)
    (hσ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (Φ : ℝ → ℂ)
    (hW : ∀ z : (InfiniteAdeleRing ℚ)ˣ,
      W (iotaGL (diagUnitGL2 z) * 1) = Φ (StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)))
    (hΦ : MeasureTheory.AEStronglyMeasurable Φ MeasureTheory.volume) (s : ℂ) :
    0 < κ ∧
      archZeta30 ν_mul W (σ.comp E) s 1 =
        (κ : ℂ) * ∫ y : ℝ, Φ y * ArchR.quasiChar t (e : ZMod 2) y * ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹ := by sorry
