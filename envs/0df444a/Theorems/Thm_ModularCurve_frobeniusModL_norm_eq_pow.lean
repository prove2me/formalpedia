-- Prove2me | Theorems.Thm_ModularCurve_frobeniusModL_norm_eq_pow
-- name    : ModularCurve.frobeniusModL_norm_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/0505b1b7-2ac0-59b9-bc9a-ae81fb37bd89
-- title:
--   Norm along the Frobenius of the modular function field is the ℓ-th power
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $\ell$ with $\ell$ prime, and let $N$ be a nonzero natural number. Inside the field $\mathrm{LaurentSeries}\,K$ consider the intermediate field $F =$ `modularFunctionFieldFullC K N`, obtained by adjoining to $K$ the set of Laurent series $\mathrm{qExpand}\,K\,d\,(\mathtt{jqModC}\,K)$ for the nonzero divisors $d$ of $N$, where $\mathrm{qExpand}\,K\,d$ is the ring endomorphism of Laurent series that multiplies all exponents by $d$ (substitution $q \mapsto q^{d}$). Let $\Phi =$ `frobeniusModL K N ℓ` be the $K$-algebra endomorphism of $F$ given by $\mathrm{qExpand}\,K\,\ell$, i.e. $x(q) \mapsto x(q^{\ell})$. Assume `FiniteAlong K` $\Phi$, that is, that $F$ is a finite module over itself for the $F$-algebra structure `algebraAlong` $\Phi$ in which scalars act through $\Phi$. Then for every $g \in F$, applying $\Phi$ to the norm of $g$ taken with respect to this algebra structure gives $g^{\ell}$: $\Phi\big(N_{\Phi}(g)\big) = g^{\ell}$.
--
--   This is the norm formula for the purely inseparable degree-$\ell$ extension $F/\Phi(F)$ of the modular function field in characteristic $\ell$: the norm along the Frobenius correspondence is the $\ell$-th power map. It feeds the computation of $q$-expansion differences along the Frobenius correspondence, used in identifying the reduction of the modular curve correspondence modulo $\ell$ with the graph of Frobenius and its transpose.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_frobeniusModL_norm_eq_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve AlgebraicCurve

theorem ModularCurve.frobeniusModL_norm_eq_pow
    (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N]
    (hfin : AlgebraicCurve.FiniteAlong K (frobeniusModL K N ℓ))
    (g : modularFunctionFieldFullC K N) :
    frobeniusModL K N ℓ
        (letI := AlgebraicCurve.algebraAlong (frobeniusModL K N ℓ)
         Algebra.norm (↥(modularFunctionFieldFullC K N)) g) = g ^ ℓ := by sorry
