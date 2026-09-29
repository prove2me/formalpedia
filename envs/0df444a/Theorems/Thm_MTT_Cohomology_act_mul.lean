-- Prove2me | Theorems.Thm_MTT_Cohomology_act_mul
-- name    : MTT.Cohomology.act_mul
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T01:43:11.860179+00:00
-- url     : https://prove2.me/theorems/45b57da8-d71e-4fd9-9f5f-73111527cae9
-- title:
--   The coefficient action is multiplicative: $\gamma\cdot(\delta\cdot P)=(\gamma\delta)\cdot P$
-- statement:
--   For a commutative ring $R$, the coefficient action of an integral $2\times 2$ matrix $\gamma$ on binary polynomials $P\in R[X_0,X_1]$ is the algebra substitution
--   $$(\gamma\cdot P)(X_0,X_1)\;=\;P\Bigl(\sum_a \gamma_{a0}X_a,\ \sum_a \gamma_{a1}X_a\Bigr),$$
--   i.e. $P\mapsto P\bigl((X_0,X_1)\gamma\bigr)$. The claim is that this is functorial in the matrix:
--   $$\gamma\cdot(\delta\cdot P)\;=\;(\gamma\delta)\cdot P$$
--   for all integral matrices $\gamma,\delta$ and all $P$.
--
--   Note that no invertibility is assumed: $\gamma$ and $\delta$ range over the full monoid $M_2(\mathbf Z)$, which is what is needed for Hecke correspondences, where the matrices occurring have determinant $\ell$ rather than $1$. Because the substitution is a *right* action written on the left, the identity reads $\gamma\cdot(\delta\cdot P)=(\gamma\delta)\cdot P$ and not $(\delta\gamma)\cdot P$; the composite substitution sends $X_i$ to $\sum_a\delta_{ai}\sum_b\gamma_{ba}X_b=\sum_b(\gamma\delta)_{bi}X_b$.
-- source:
--   Standard functoriality of the right coefficient action on Sym^n; cf. Ash-Stevens, Modular forms in characteristic l and special values of their L-functions, Duke Math. J. 53 (1986), section 1, pp. 850-852, https://math.bu.edu/people/ghs/papers/Mod_fms_char_ell.pdf

import Definitions.Def_MTT_Cohomology
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT.Cohomology

theorem MTT.Cohomology.act_mul {R : Type*} [CommRing R]
    (γ δ : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary R) :
    act γ (act δ P) = act (γ * δ) P := by sorry
