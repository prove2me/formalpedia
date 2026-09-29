-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersSnd_iff_coe_frickeInvolutionBar_mem_modularLocalized
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_integersSnd_iff_coe_frickeInvolutionBar_mem_modularLocalized
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/470b356d-8bd8-5dfc-9f6b-ff7ba1411856
-- title:
--   Second prolongation integers as Fricke pull-back of localised reduction
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A \to k$. Fix further data entering the level-one specialisation package: a modular polynomial datum $\mathit{data}$ for $q$ (a monic $\Phi \in (\mathbb Z[X])[Y]$ of degree $\psi(q)$ annihilating the $q$-expansion pair), a proof $h_{\mathrm{Kr}}$ of the Kronecker congruence $\Phi \bmod q = (X^{q}-Y)(X-Y^{q})$ in the bivariate normalisation used here, integrality hypotheses $h_\alpha$, $h_\beta$ for the two Hecke maps $\overline{\alpha}$, $\overline{\beta}$ at level $1$ and prime $q$ over $\overline{\mathbb Q}$, and a place specialisation $P$ for these data with values in $k$. Let $R$ be a level-one prolongation pair for $P$, so in particular $R$ carries two regular prolongations $R_1$, $R_2$ of $A$ to the function field $\mathrm{modularFunctionFieldBar}(1\cdot q)$ (the base change to $\overline{\mathbb Q}$ of the full modular function field of level $1\cdot q$ inside $\overline{\mathbb Q}((\mathfrak q))$), linked by the clause $f \in R_2 \iff w\,f \in R_1$, together with the dictionary clause comparing the residue of $R_1$ with the localised reduction. Then for every $g$ in that function field, $g$ belongs to the valuation subring $R.R_2.\mathrm{integers}$ if and only if the Laurent series underlying $\mathrm{frickeInvolutionBar}(1\cdot q)\,g$ lies in $\mathrm{CharPReduction.modularLocalized}(1\cdot q)$ for $A$ and $\mathrm{red}$, i.e. there exist $r,s$ in the modular ring over $A$ with $s$ outside the prime ideal of elements with vanishing coefficientwise reduction and $(w\,g)\cdot s = r$.
--
--   This is the Fricke-transported half of the dictionary between the two descriptions of integrality on $X_0(q)$ used in the reduction argument: the valuation-theoretic one given by the prolongation pair, and the explicit one given by the localised presentation ring of $q$-expansions over $A$. It is used in the verification of the regularity and chart laws for the level-one model, and in the statements about orders of residues and values of products.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersSnd_iff_coe_frickeInvolutionBar_mem_modularLocalized.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_integersSnd_iff_coe_frickeInvolutionBar_mem_modularLocalized
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (g : ↥(modularFunctionFieldBar (1 * q))) :
    g ∈ R.R₂.integers ↔
      ((frickeInvolutionBar (1 * q) g : ↥(modularFunctionFieldBar (1 * q))) :
          LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by sorry
