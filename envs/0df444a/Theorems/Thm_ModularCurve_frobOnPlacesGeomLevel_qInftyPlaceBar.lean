-- Prove2me | Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_qInftyPlaceBar
-- name    : ModularCurve.frobOnPlacesGeomLevel_qInftyPlaceBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/3fa9825f-7814-5c19-9529-92225e569a14
-- title:
--   Frobenius on places fixes the q-adic infinite place
-- statement:
--   Let $k$ be a field of characteristic $\ell$, where $\ell$ is prime, and let $N$ be a positive integer. Let $F =$ `modularFunctionFieldC k N` be the intermediate field of the Laurent series field $k((q))$ generated over $k$ by the two series `jqModC k` (the $j$-series, $q^{-1}$ times the integral power series `jNum` reduced into $k$) and `jqNModC k N` (its image under the substitution `qExpand k N`). Let `data` be a modular polynomial datum of level $\ell$, that is a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(\ell)$ with $\Phi(j, j_\ell) = 0$, and assume the Kronecker congruence `hKr`: the coefficientwise reduction of $\Phi$ modulo $\ell$ equals $(C X^{\ell} - X)\,(C X - X^{\ell})$. Assume further that some element of $F$ has Laurent-series order exactly $-1$. Under these hypotheses the place `qInftyPlaceBar`, whose valuation subring is $\{f \in F : \operatorname{ord}_q f \ge 0\}$ (the order hypothesis giving that it is proper and a principal ideal ring), is fixed by the Frobenius operator `frobOnPlacesGeomLevel k N data hKr`, which restricts a place of $F$ to the image $\mathrm{qExpandAlgC}_{k,\ell}(F) \subseteq F$ and transports it back along the isomorphism of $F$ with that image.
--
--   This is the place-theoretic form of the statement that the cusp $\infty$ of the modular curve in characteristic $\ell$ is fixed by the Frobenius correspondence coming from the Kronecker congruence for the modular polynomial; no coprimality of $N$ with $\ell$ is assumed and $k$ need not be finite. It is used by [`ModularCurve.CharPModel.frobOnPlacesGeomLevel_eq_self_of_ord_jqModC_neg`](thm.html#ModularCurve.CharPModel.frobOnPlacesGeomLevel_eq_self_of_ord_jqModC_neg) in the analysis of the characteristic-$\ell$ model of the modular function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_frobOnPlacesGeomLevel_qInftyPlaceBar.lean

import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.frobOnPlacesGeomLevel_qInftyPlaceBar (k : Type*) [Field k] (N : ℕ) [NeZero N]
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (h : ∃ j : modularFunctionFieldC k N, (qSeriesBar k (modularFunctionFieldC k N) j).order = -1) :
    frobOnPlacesGeomLevel k N data hKr (qInftyPlaceBar k (modularFunctionFieldC k N) h)
      = qInftyPlaceBar k (modularFunctionFieldC k N) h := by sorry
