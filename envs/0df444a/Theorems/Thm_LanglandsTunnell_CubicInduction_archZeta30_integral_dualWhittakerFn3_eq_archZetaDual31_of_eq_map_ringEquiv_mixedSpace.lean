-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_archZeta30_integral_dualWhittakerFn3_eq_archZetaDual31_of_eq_map_ringEquiv_mixedSpace
-- name    : LanglandsTunnell.CubicInduction.archZeta30_integral_dualWhittakerFn3_eq_archZetaDual31_of_eq_map_ringEquiv_mixedSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/bba257aa-d578-5833-a6da-b9801376721a
-- title:
--   Dual archimedean (3,1) zeta integral of a unipotent average
-- statement:
--   Fix measurable-space structures on $\mathbb{A}_\infty^\times=(\mathrm{InfiniteAdeleRing}\ \mathbb{Q})^\times$ and on $\mathbb{A}_\infty$, the latter Borel, a measure $\nu_{\mathrm{mul}}$ on $\mathbb{A}_\infty^\times$ and a measure $\nu_{\mathrm{add}}$ on $\mathbb{A}_\infty$, and assume $\nu_{\mathrm{add}}$ is the push-forward of Lebesgue measure on the mixed space $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ of $\mathbb{Q}$ along the inverse of the canonical ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace`. Let $W:\mathrm{GL}_3(\mathbb{A}_\infty)\to\mathbb{C}$ be a function, $\sigma:\mathbb{A}_\infty^\times\to\mathbb{C}^\times$ a monoid homomorphism, $s\in\mathbb{C}$ and $g\in\mathrm{GL}_3(\mathbb{A}_\infty)$. Write $\tilde{W}(m)=W(w_3\,{}^t m^{-1})$ for the dual function, $w_3$ the antidiagonal permutation matrix, $w'$ the matrix interchanging the last two coordinates, $u(x)$ the lower unipotent matrix with entry $x$ in position $(2,1)$, and $a\mapsto\mathrm{diag}(a,1)$ embedded into the upper-left $2\times2$ block of $\mathrm{GL}_3$. The assertion is the equality of $$\int_{\mathbb{A}_\infty^\times}\Big(\int_{\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}}\tilde{W}\big(\mathrm{diag}(a,1,1)\,u(\iota^{-1}y)\,w'\,{}^t g^{-1}\big)\,dy\Big)\,\sigma(a)^{-1}\,\|a\|^{s-1}\,d\nu_{\mathrm{mul}}$$ (the $\mathrm{GL}_1$-type zeta integral `archZeta30` of the inner average, at $\sigma^{-1}$ and identity translate) with $\mathrm{archZetaDual31}$ at $\nu_{\mathrm{mul}},\nu_{\mathrm{add}}$ of the right translate $h\mapsto W(hg)$, namely the same double integral with $\nu_{\mathrm{add}}$ in place of $dy$, the dual of $W(\cdot\,g)$ in place of $\tilde W$, and $w'\,{}^t 1^{-1}$ in place of $w'\,{}^t g^{-1}$.
--
--   This identifies the archimedean factor produced by the $S$-part factorisation of the dual global $(3,1)$ zeta integral with the dual archimedean zeta integral in the normalisation used for the archimedean functional equations of the cubic-induction argument. It is used in the assembly of the global functional equation and root-number identities for the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_archZeta30_integral_dualWhittakerFn3_eq_archZetaDual31_of_eq_map_ringEquiv_mixedSpace.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg

open scoped Classical in

theorem LanglandsTunnell.CubicInduction.archZeta30_integral_dualWhittakerFn3_eq_archZetaDual31_of_eq_map_ringEquiv_mixedSpace
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ]
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (σ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) (s : ℂ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archZeta30 ν_mul (fun h => ∫ y : mixedEmbedding.mixedSpace ℚ,
        dualWhittakerFn3 W (h * lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) *
          (weylPrime3 * transposeInv3 g))) σ⁻¹ s 1 =
      archZetaDual31 ν_mul ν_add (fun h => W (h * g)) σ s 1 := by sorry
