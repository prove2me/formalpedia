-- Prove2me | Theorems.Thm_ModularCurve_exists_subalgebra_isDedekindDomain_isFractionRing_mem_iff_isIntegral_jModElt
-- name    : ModularCurve.exists_subalgebra_isDedekindDomain_isFractionRing_mem_iff_isIntegral_jModElt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/aadd12fc-e7d8-5932-8d4e-1eb97b045397
-- title:
--   Integral closure of K[̃ j] in F_N is Dedekind
-- statement:
--   Let $K$ be a field with decidable equality and let $N$ be a nonzero natural number whose image in $K$ is nonzero, so that the characteristic of $K$ does not divide $N$. Write $\tilde j =$ [`ModularCurve.jqModC K`](def/ModularCurve_JqCoeff.html#L15) for the Laurent series $q^{-1}\cdot \iota(\mathrm{jNum})$ over $K$, the image of the integral power series $\mathrm{jNum}$ shifted by $q^{-1}$, and let $F_N =$ [`ModularCurve.modularFunctionFieldFullC K N`](def/ModularCurve_X0ModL.html#L100) be the intermediate field of $K \subseteq K((q))$ obtained by adjoining to $K$ the set of all `qExpand K d`-images of $\tilde j$ for nonzero divisors $d \mid N$. Inside $F_N$ let $\tilde j$ also denote the element [`ModularCurve.jModElt`](def/ModularCurve_QAdicPlaceMod.html#L80) determined by the membership $\tilde j \in F_N$. The assertion is that there is a $K$-subalgebra $A$ of $F_N$ such that $A$ is a Dedekind domain, $F_N$ is a fraction field of $A$, and an element $a \in F_N$ lies in $A$ if and only if there is a monic polynomial $P \in (K[X])[Y]$ with $P(a) = 0$ after substituting $\tilde j$ for $X$; that is, $A$ is exactly the set of elements of $F_N$ integral over the subring $K[\tilde j]$.
--
--   This is the normal affine model of the level-$N$ modular curve over the $j$-line: the integral closure $\tilde R$ of the polynomial ring $K[\tilde j]$ in the level-$N$ modular function field is a Dedekind domain with fraction field $F_N$, so that places of $F_N/K$ lying over finite values of $j$ correspond to maximal ideals of $\tilde R$. It is used by [`ModularCurve.eq_of_isModuliPlaceOf`](thm.html#ModularCurve.eq_of_isModuliPlaceOf), the uniqueness statement for the moduli place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_subalgebra_isDedekindDomain_isFractionRing_mem_iff_isIntegral_jModElt.lean

import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ModularCurve.exists_subalgebra_isDedekindDomain_isFractionRing_mem_iff_isIntegral_jModElt
    (K : Type u) [Field K] [DecidableEq K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    ∃ A : Subalgebra K ↥(ModularCurve.modularFunctionFieldFullC K N),
      IsDedekindDomain ↥A ∧ IsFractionRing ↥A ↥(ModularCurve.modularFunctionFieldFullC K N) ∧
        ∀ a : ↥(ModularCurve.modularFunctionFieldFullC K N), a ∈ A ↔ (∃ P : Polynomial (Polynomial K), P.Monic ∧ Polynomial.eval₂ (Polynomial.aeval (R := K) (ModularCurve.jModElt K (ModularCurve.jqModC_mem_full K N))).toRingHom a P = 0) := by sorry
