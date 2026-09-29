-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_dualWhittakerFn3_jacquetVector3_prod
-- name    : LanglandsTunnell.CubicInduction.integrable_dualWhittakerFn3_jacquetVector3_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/7dad2467-25d3-5fed-97ac-1d934847142b
-- title:
--   Integrability of the dual GL₃ zeta integrand of a Jacquet vector
-- statement:
--   Fix a real archimedean parameter $P_2$ and a datum $D$ for it (a Whittaker-type function $W$ on $M_2(\mathbb{R})$ with the unipotent and central transformation laws, entire twisted zeta functions, their functional equation and growth and decay bounds), a complex $u_3$, a sign $a_3\in\mathbb{Z}/2$, and a monoid homomorphism $E$ from the units of the infinite adele ring of $\mathbb{Q}$ to the units of the adele ring such that for every $u$ the infinite part of $E(u)$ is $u$ and the finite part of $E(u)$ is $1$. Let $a\in\mathbb{Q}$ be nonzero and let $\mathrm{psiInf}$ be the additive character $x\mapsto \psi_{\mathrm{arch}}(ax)$ of the infinite adele ring, which carries Borel measurable structures; let $\nu_{\mathrm{add}}$ be $|a|^{1/2}$ times the pushforward of Lebesgue measure along the inverse of the identification of the infinite adele ring with the mixed space, and $\nu_{\mathrm{mul}}$ a Haar measure on its unit group. Let $S$ be a polynomial multiple of the Gaussian $M\mapsto \exp(-\pi\sum_{i,b}M_{ib}^2)$ on $2\times 3$ real matrices, and let $c_1$ be a real number with $-\operatorname{Re}\mu<c_1$ for every $\mu$ in the $\Gamma_{\mathbb{R}}$-shifts and every $\mu$ in the $\Gamma_{\mathbb{C}}$-shifts of $P_2^{\vee}$ twisted by $(0,a)$, for each sign $a\in\mathbb{Z}/2$. Let $\sigma$ be a continuous unitary idele class character of $\mathbb{Q}$ whose archimedean component at every real infinite place $v$ is $x\mapsto \|x\|^{\mathrm{mult}(v)\,t}(x/\|x\|)^{e}$, let $g_\infty\in\mathrm{GL}_3$ of the infinite adeles, and let $s$ satisfy $\max(c_1,\operatorname{Re}u_3)+\operatorname{Re}t<\operatorname{Re}s$. Then the function
--   $$(y,x)\longmapsto V\bigl(w_3\cdot{}^{t}(\iota(\mathrm{diag}(y,1))\,u_{21}(x)\,(w'\,{}^{t}1^{-1}))^{-1}\,g_\infty\bigr)\cdot\sigma(E(y))^{-1}\cdot\|y\|^{s-1},$$
--   where $V$ is the Jacquet vector $\mathrm{jacquetVector3}\,D\,u_3\,a_3\,a\,\mathrm{psiInf}\,S$, namely $g\mapsto \mathrm{quasiChar}(u_3+1,a_3)(\det g_{\mathbb{R}})\int_{M_2(\mathbb{R})}\mathrm{jacquetIntegrand3}$, is integrable on the product of the units and the additive group of the infinite adele ring with respect to $\nu_{\mathrm{mul}}\otimes\nu_{\mathrm{add}}$.
--
--   This is the absolute convergence of the dual archimedean zeta integral, in the torus-times-unipotent coordinates of the $(3,1)$ mirabolic, attached to a Jacquet vector built from a $\mathrm{GL}_2$ archimedean datum by cubic induction, for a single $s$ to the right of the dual abscissa $\max(c_1,\operatorname{Re}u_3)+\operatorname{Re}t$. It feeds the vertical-strip bound [`LanglandsTunnell.CubicInduction.forall_pow_mul_norm_archZetaDual31_jacquetVector3_le`](thm.html#LanglandsTunnell.CubicInduction.forall_pow_mul_norm_archZetaDual31_jacquetVector3_le) for the dual zeta integral, part of the analytic input to the converse theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integrable_dualWhittakerFn3_jacquetVector3_prod.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse MeasureTheory
open LanglandsTunnell LanglandsTunnell.CubicInduction in
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.integrable_dualWhittakerFn3_jacquetVector3_prod
    (P₂ : RealArchParam) (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (ha : a ≠ 0)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (c₁ : ℝ)
    (hc₁ : ∀ a : ZMod 2,
      (∀ μ ∈ (P₂.dual.twist 0 a).gammaR, -μ.re < c₁) ∧ (∀ ν ∈ (P₂.dual.twist 0 a).gammaC, -ν.re < c₁))
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hσ : IsAdmissibleTwist ℚ σ)
    (t : ℂ) (e : ℤ) (hte : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e)
    (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (s : ℂ) (hs : max c₁ u₃.re + t.re < s.re) :
    Integrable (fun p : (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ =>
      dualWhittakerFn3 (fun h => jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S (h * gInf))
          (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * (weylPrime3 * transposeInv3 1)) *
        ((((σ.comp E)⁻¹ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) p.1 : ℂˣ) : ℂ) *
        ((‖(p.1 : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)) (ν_mul.prod ν_add) := by sorry
