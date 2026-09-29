-- Prove2me | Theorems.Thm_ModularCurve_coeff_qExpansionDiffAlong_kw_cart_C_pow
-- name    : ModularCurve.coeff_qExpansionDiffAlong_kw_cart_C_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/93a7a634-9e6f-5ebb-9ea0-0adf58043fcf
-- title:
--   Cartier operator on q-expansions: aₙ(Cω)ᵖ=aₙₚ(ω)
-- statement:
--   Let $K$ be a field and $p$ a prime. Let $F$ be an intermediate field of the Laurent series field $K((q))$ over $K$ whose characteristic is $p$, and let $t\in F$ be such that: the universal derivation $d t = \mathrm{D}_{K/F}t\in\Omega_{F/K}$ is nonzero; the $F$-span of $\{dt\}$ is all of $\Omega_{F/K}$; every $x\in F$ is separable over the subfield underlying $\mathrm{kw\_pke\_expansionField}$ of $t$, namely the subfield of $F$ generated over the image $F^p$ of the Frobenius endomorphism by $t$; and the minimal polynomial of $t$ over the subfield $F^p$ of $p$-th powers has degree $p$. Write $C\omega$ for `kw_cart_C`, the differential obtained from $\omega\in\Omega_{F/K}$ by expressing $\omega=f\,dt$ with $f\in F$ (possible by the spanning hypothesis), writing $f=\sum_{i<p}c_i t^i$ with coefficients $c_i\in F^p$ (possible by the separability and degree hypotheses), choosing a $p$-th root $c$ of the coefficient $c_{p-1}$ and setting $C\omega=c\,dt$. Let $a_n(\cdot)\in K$ denote the $n$-th coefficient of the Laurent series obtained by applying `qExpansionDiffAlong` of the inclusion $F\hookrightarrow K((q))$, that is, the $K$-linear map $\Omega_{F/K}\to K((q))$ determined, when one exists, by $x\,dy\mapsto x\cdot\theta(y)$ with $\theta=q\,d/dq$ on Laurent series, and taken to be $0$ otherwise. Then for all $\omega\in\Omega_{F/K}$ and all $n\in\mathbb Z$ one has $a_n(C\omega)^p=a_{np}(\omega)$.
--
--   This is the classical description of the Cartier operator on $q$-expansions of differentials, $C\bigl(\sum a_n q^n\,dq/q\bigr)=\sum a_{np}^{1/p}q^n\,dq/q$, here formulated for an arbitrary intermediate field of $K((q))$ possessing a separating coordinate $t$, so that it is available at every modular level. It is used in the treatment of the Cartier operator on $q$-expansions of modular differentials and in the construction of Frobenius-compatible expansions for the modular curves $X_H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_qExpansionDiffAlong_kw_cart_C_pow.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_KwCartierOperatorTCoordEngine
import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve.KwCart AlgebraicCurve.KwPke
set_option synthInstance.maxHeartbeats 200000 in

theorem ModularCurve.coeff_qExpansionDiffAlong_kw_cart_C_pow
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime]
    (F : IntermediateField K (LaurentSeries K)) [CharP F p] (t : F)
    (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := p) t).toSubfield x)
    (hdeg : (minpoly (kw_pke_pthPowers F p) t).natDegree = p)
    (ω : Ω[F⁄K]) (n : ℤ) :
    (qExpansionDiffAlong F.val (kw_cart_C (K := K) t hdt hspan hsep hdeg ω)).coeff n ^ p
      = (qExpansionDiffAlong F.val ω).coeff (n * p) := by sorry
