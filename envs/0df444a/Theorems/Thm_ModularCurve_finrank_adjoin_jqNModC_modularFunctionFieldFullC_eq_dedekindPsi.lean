-- Prove2me | Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_modularFunctionFieldFullC_eq_dedekindPsi
-- name    : ModularCurve.finrank_adjoin_jqNModC_modularFunctionFieldFullC_eq_dedekindPsi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/dc06d3ed-fd1f-5dac-929d-d42deec57def
-- title:
--   Degree ψ(N) of the modular function field over K(j_N)
-- statement:
--   Let $K$ be a field and $N$ a positive integer such that the image of $N$ in $K$ is nonzero. Work inside the field $K((q))$ of Laurent series over $K$. Write $\bar j =$ `jqModC K` for the Laurent series $q^{-1}\cdot(\text{image of the power series } \mathtt{jNum} \text{ under } \mathbb{Z}\to K)$, i.e. the coefficientwise reduction to $K$ of the $q$-expansion of the modular invariant $j$, and for $d\ge 1$ let `qExpand K d` be the ring endomorphism of $K((q))$ multiplying all exponents by $d$, so that `qExpand K d` $\bar j$ is '$\bar j(q^d)$'. Let $\bar F_N =$ `modularFunctionFieldFullC K N` be the intermediate field of $K((q))/K$ generated over $K$ by the set of all $\bar j(q^d)$ with $d$ a positive divisor of $N$, and let $\bar j_N =$ `jqNModC K N` $=$ `qExpand K N` $\bar j$, which lies in $\bar F_N$. The assertion is that $\bar F_N$, viewed as a module over the intermediate field $K(\bar j_N)\subseteq \bar F_N$ obtained by adjoining the single element $\bar j_N$ to $K$, has finite rank equal to `dedekindPsi N` $=\sum_{d\mid N,\ d\ \text{squarefree}} N/d$, the Dedekind $\psi$-function $N\prod_{p\mid N}(1+1/p)$.
--
--   This is the companion, for the coordinate $\bar j_N=\bar j(q^N)$, of the statement that $[\bar F_N : K(\bar j)]=\psi(N)$, reflecting classically the symmetry of the modular equation $\Phi_N$ (equivalently the Fricke involution of $X_0(N)$); over fields whose characteristic does not divide $N$ it is Igusa's theorem on reduction of the modular function field. It is used in the computation of relative degrees inside `modularFunctionFieldFullC` and in the analysis of places and coordinates on the reduced modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_adjoin_jqNModC_modularFunctionFieldFullC_eq_dedekindPsi.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.finrank_adjoin_jqNModC_modularFunctionFieldFullC_eq_dedekindPsi
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    Module.finrank
        (IntermediateField.adjoin K
          ({⟨jqNModC K N, modularFunctionFieldC_le_full K N (jqNModC_mem K N)⟩} :
            Set (modularFunctionFieldFullC K N)))
        (modularFunctionFieldFullC K N) = dedekindPsi N := by sorry
