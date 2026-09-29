-- Prove2me | Theorems.Thm_ModularCurve_coeffMap_mem_modularFunctionFieldC
-- name    : ModularCurve.coeffMap_mem_modularFunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/232d73c2-54d2-51b6-b788-7dba8cd86198
-- title:
--   Coefficientwise reduction preserves the modular function field
-- statement:
--   Let $L$ be a field and $O \subseteq L$ a subring which is a valuation ring and which satisfies the hypothesis that for every $z \in L$ either $z \in O$ or $z^{-1} \in O$. Let $K$ be a field, let $\mathrm{res} : O \to K$ be a ring homomorphism, and let $N$ be a nonzero natural number. Here $\mathtt{jqModC}\,R$ denotes, for a commutative ring $R$, the Laurent series $q^{-1}$ times the image over $R$ of the integral power series $\mathtt{jNum} = E_4^3 \cdot \eta^{-24}$, i.e. the $q$-expansion of $j$; $\mathtt{jqNModC}\,R\,N$ is its image under the ring endomorphism `qExpand` of $\mathrm{LaurentSeries}\,R$ which multiplies all exponents by $N$ (substitution $q \mapsto q^N$); and $\mathtt{modularFunctionFieldC}\,R\,N$ is the intermediate field $R(\mathtt{jqModC}\,R, \mathtt{jqNModC}\,R\,N)$ of $\mathrm{LaurentSeries}\,R$. Assume the degree hypothesis that $K(\mathtt{jqModC}\,K)(\mathtt{jqNModC}\,K\,N)$ has finite rank exactly $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$ over $K(\mathtt{jqModC}\,K)$. Let $x$ be a Laurent series over $L$ lying in $\mathtt{modularFunctionFieldC}\,L\,N$, and suppose $x$ is the coefficientwise image, under the inclusion $O \hookrightarrow L$, of a Laurent series $y$ with coefficients in $O$. Then the coefficientwise image of $y$ under $\mathrm{res}$ lies in $\mathtt{modularFunctionFieldC}\,K\,N$. Surjectivity of $\mathrm{res}$ is not assumed, and `coeffMap` is the ring homomorphism on Laurent series induced by applying a ring homomorphism to each coefficient.
--
--   This is the membership half of the $q$-expansion principle on the $j$-line: an element of $L(j(q), j(q^N))$ whose $q$-expansion has coefficients in the valuation ring $O$ reduces, coefficient by coefficient, into $K(j(q), j(q^N))$, provided the level-$N$ degree over $K$ has its generic value $\psi(N)$ (a hypothesis that genuinely fails in residue characteristic dividing $N$, where the Kronecker congruence intervenes). It is used in the analysis of mod $p$ forms, in [`ModPForms.exists_coe_mul_thetaL_jqModC_pow_eq_ofPowerSeries_of_mem_modPMod`](thm.html#ModPForms.exists_coe_mul_thetaL_jqModC_pow_eq_ofPowerSeries_of_mem_modPMod).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeffMap_mem_modularFunctionFieldC.lean

import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import Mathlib.RingTheory.Valuation.ValuationRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.coeffMap_mem_modularFunctionFieldC {L : Type*} [Field L] (O : Subring L)
    [ValuationRing O] (hO : ∀ z : L, z ∈ O ∨ z⁻¹ ∈ O) {K : Type*} [Field K] (res : O →+* K)
    (N : ℕ) [NeZero N]
    (hdeg : Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
        ({jqNModC K N} : Set (LaurentSeries K))) = dedekindPsi N)
    {x : LaurentSeries L} (hx : x ∈ modularFunctionFieldC L N)
    (y : LaurentSeries O) (hy : coeffMap O.subtype y = x) :
    coeffMap res y ∈ modularFunctionFieldC K N := by sorry
