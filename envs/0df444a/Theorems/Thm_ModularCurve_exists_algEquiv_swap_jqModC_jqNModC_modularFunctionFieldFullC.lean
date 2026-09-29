-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC
-- name    : ModularCurve.exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/975586f0-bf2e-5b3e-a1a7-19d2f33ea14e
-- title:
--   A Fricke involution exchanging j(q) and j(q^N)
-- statement:
--   Let $K$ be a field and let $N$ be a positive natural number whose image in $K$ is nonzero. Inside the field $K((q))$ of Laurent series over $K$, write $j$ for the element `jqModC K`, namely $q^{-1}$ times the image in $K[[q]]$ of the integral power series $E_4^3 \cdot \eta^{-24}$ (the $q$-expansion of the modular invariant with coefficients read in $K$), and for a positive $d$ let `qExpand K d` be the ring endomorphism of $K((q))$ substituting $q \mapsto q^d$ (multiplication by $d$ on exponents). Let $F_N =$ `modularFunctionFieldFullC K N` be the intermediate field of $K((q))$ obtained by adjoining to $K$ the set of all $q$-expansions `qExpand K d (jqModC K)` with $d$ a positive divisor of $N$; in particular $j$ itself (the case $d = 1$) and $j_N =$ `jqNModC K N` $=$ `qExpand K N (jqModC K)` (the case $d = N$) lie in $F_N$. The assertion is that there exists a $K$-algebra isomorphism $\sigma$ of $F_N$ with itself such that $\sigma(j) = j_N$, $\sigma(j_N) = j$, and $\sigma(\sigma(x)) = x$ for every $x \in F_N$.
--
--   This is the algebraic form, over an arbitrary field in which $N$ is invertible, of the Fricke involution $w_N : \tau \mapsto -1/(N\tau)$ acting on the function field of $X_0(N)$ and exchanging $j(\tau)$ with $j(N\tau)$. It is used in the comparison of degrees and relative ranks of subfields of the full modular function field at level $N$, where the symmetry between the two principal generators $j$ and $j_N$ transfers rank computations from one to the other.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    ∃ σ : modularFunctionFieldFullC K N ≃ₐ[K] modularFunctionFieldFullC K N,
      σ ⟨jqModC K, jqModC_mem_full K N⟩ = ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ ∧
      σ ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ = ⟨jqModC K, jqModC_mem_full K N⟩ ∧
      ∀ x, σ (σ x) = x := by sorry
