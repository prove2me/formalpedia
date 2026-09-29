-- Prove2me | Theorems.Thm_ModularCurve_isSeparable_and_finrank_adjoin_aeval_jqModC_modularFunctionFieldFullC
-- name    : ModularCurve.isSeparable_and_finrank_adjoin_aeval_jqModC_modularFunctionFieldFullC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/b17686f2-905b-5405-89db-55b0621a5f7a
-- title:
--   Polynomials in jmath̄ as separating elements of degree deg r·ψ(N)
-- statement:
--   Let $K$ be a field, let $N$ be a nonzero natural number whose image in $K$ is nonzero, and let $r \in K[X]$ be a polynomial with $r' \neq 0$. Write $\bar\jmath =$ `jqModC K` for the Laurent series $q^{-1}\cdot\iota(\mathrm{jNum})$ in $K((q))$, where $\mathrm{jNum} = E_4^3 \cdot \mathrm{dedekindEtaUnitInv}$ in $\mathbb{Z}[[q]]$ and $\iota$ is coefficientwise reduction along $\mathbb{Z} \to K$; thus $\bar\jmath$ is the $q$-expansion of the modular invariant over $K$. Let $F =$ `modularFunctionFieldFullC K N` be the intermediate field of $K((q))$ generated over $K$ by the set of Laurent series `qExpand K d (jqModC K)` for the nonzero divisors $d$ of $N$. The series $\bar\jmath$ itself lies in $F$ (the divisor $d = 1$), and $r$ may be evaluated at this element of $F$. The assertion is twofold: $F$ is a separable algebraic extension of the intermediate field $K(r(\bar\jmath))$ generated over $K$ by that single element, and $$[F : K(r(\bar\jmath))] = \deg r \cdot \psi(N), \qquad \psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d,$$ the degree being the natural degree of $r$ and $\psi$ the Dedekind psi function in the stated summation form.
--
--   This identifies $r(\bar\jmath)$, for any $r$ with nonvanishing derivative (in characteristic $p$ this says precisely that $r$ is not a polynomial in $X^p$), as a separating element of the full level-$N$ modular function field over $K$, together with the degree of the resulting extension; the case $r = X^p + X$ produces the function $\bar\jmath + \bar\jmath^{\,p}$ on the special fibre of $X_0(Np)$. It is used in the construction of the coordinate ring of the corresponding chart, in [`ModularCurve.isDedekindDomain_and_finite_and_isSeparable_chartRing_jqModC`](thm.html#ModularCurve.isDedekindDomain_and_finite_and_isSeparable_chartRing_jqModC), and rests on the degree computation [`ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi`](thm.html#ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi) and on the separability of the $q$-expansions `jqNModC` over $K(\bar\jmath)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isSeparable_and_finrank_adjoin_aeval_jqModC_modularFunctionFieldFullC.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.isSeparable_and_finrank_adjoin_aeval_jqModC_modularFunctionFieldFullC
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (r : Polynomial K) (hr : Polynomial.derivative r ≠ 0) :
    Algebra.IsSeparable
        (IntermediateField.adjoin K
          ({Polynomial.aeval (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) r} :
            Set (modularFunctionFieldFullC K N)))
        (modularFunctionFieldFullC K N) ∧
    Module.finrank
        (IntermediateField.adjoin K
          ({Polynomial.aeval (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) r} :
            Set (modularFunctionFieldFullC K N)))
        (modularFunctionFieldFullC K N) = r.natDegree * dedekindPsi N := by sorry
