-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_frobOnPlacesGeomLevel_eq_self_of_ord_jqModC_neg
-- name    : ModularCurve.CharPModel.frobOnPlacesGeomLevel_eq_self_of_ord_jqModC_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/9efff31a-f4d3-56d3-8410-446a0ee7c005
-- title:
--   Geometric Frobenius fixes the poles of ̃ j
-- statement:
--   Let $k$ be a field, $N$ a positive integer, and $\ell$ a prime with $k$ of characteristic $\ell$. Let `data` be a datum `ModularPolynomialData ℓ`, that is a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(\ell)$ annihilating the pair of $q$-expansions $(j, j_\ell)$, and let `hKr` assert the Kronecker congruence for it: the reduction of $\Phi$ modulo $\ell$ equals $(C(X)^{\ell}-X)\,(C(X)-X^{\ell})$ in $(\mathbb{Z}/\ell)[X][Y]$. Assume $N$ is squarefree and $\ell \nmid N$. Let $F$ be `modularFunctionFieldC k N`, the subfield of the Laurent series field $k((q))$ generated over $k$ by $\tilde j =$ `jqModC k` (namely $q^{-1}$ times the reduction to $k$ of the integral power series `jNum`) and by its $N$-fold $q$-substitution `jqNModC k N`. Let $P$ be a place of $F$ over $k$, i.e. a proper valuation subring of $F$ containing $k$ whose ideals are principal, and suppose $\mathrm{ord}_P(\tilde j) < 0$, the order being minus the logarithm of the associated adic valuation. Then `frobOnPlacesGeomLevel k N data hKr P = P`: the place obtained by restricting $P$ to the image of $F$ under the $\ell$-power $q$-substitution and transporting it back along the induced isomorphism equals $P$.
--
--   In classical terms the places at which $\tilde j$ has a pole are the cusps of $X_0(N)$ in its function-field model; for squarefree level these are fixed by the geometric Frobenius of the characteristic-$\ell$ model. The result feeds the analysis of Hecke divisors and of the component group at places of the special fibre, being used by [`ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_heckeDivBar_of_mem_principal`](thm.html#ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_heckeDivBar_of_mem_principal) and by the component-group computation [`ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div_levelOne_of_five_le`](thm.html#ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div_levelOne_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_frobOnPlacesGeomLevel_eq_self_of_ord_jqModC_neg.lean

import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.CharPModel.frobOnPlacesGeomLevel_eq_self_of_ord_jqModC_neg
    (k : Type*) [Field k] (N : ℕ) [NeZero N]
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (hsq : Squarefree N) (hlN : ¬ ℓ ∣ N)
    (P : Place k (modularFunctionFieldC k N))
    (hpole : P.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0) :
    frobOnPlacesGeomLevel k N data hKr P = P := by sorry
