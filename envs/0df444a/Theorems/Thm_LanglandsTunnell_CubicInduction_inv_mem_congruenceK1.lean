-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_inv_mem_congruenceK1
-- name    : LanglandsTunnell.CubicInduction.inv_mem_congruenceK1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/44084459-407d-5770-86c8-d7e5e2ef4609
-- title:
--   The congruence set K₁(𝔭ᵥᶜ) in GL₃ is inverse-closed
-- statement:
--   Let $R$ be a Dedekind domain with field of fractions $K$ (the algebra structure and fraction-field property being part of the data), let $v$ be a height-one prime of $R$, and let $v.\mathrm{adicCompletion}\,K$ be the completion of $K$ at $v$ with its valuation $\mathrm{Valued.v}$ taking values in $\mathbb{Z}^{\mathrm{m}0}$-style multiplicative group written through $\mathrm{WithZero.exp}$. Fix a natural number $c$ and an element $k$ of $\mathrm{GL}(\mathrm{Fin}\ 3, v.\mathrm{adicCompletion}\,K)$. The hypothesis is that $k$ lies in `congruenceK1 R K v c`, that is: (i) $k$ lies in the subgroup `localMaximalCompact3 R K v`, meaning every entry of the matrix of $k$ and every entry of the matrix of $k^{-1}$ has valuation $\le 1$; and (ii) the bottom row of $k$ is congruent to $(0,0,1)$ in the sense that $\mathrm{Valued.v}(k_{2,0})$, $\mathrm{Valued.v}(k_{2,1})$ and $\mathrm{Valued.v}(k_{2,2}-1)$ are all $\le \mathrm{WithZero.exp}(-c)$. The conclusion is that $k^{-1}$ again lies in `congruenceK1 R K v c`, i.e. satisfies the same integrality-with-inverse condition and the same three bottom-row congruences.
--
--   This is the closure under inversion of the mirabolic congruence set $K_1(\mathfrak{p}_v^c)\subset \mathrm{GL}_3(K_v)$, whose defining conditions are integrality of a matrix together with its inverse and congruence of the bottom row to $(0,0,1)$ modulo $\mathfrak{p}_v^c$. It is used where level-$c$ invariance under this set is exploited, in the construction of normalised new vectors from local Whittaker data in the cubic-induction and Rankin–Selberg parts of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_inv_mem_congruenceK1.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain

theorem
LanglandsTunnell.CubicInduction.inv_mem_congruenceK1
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) {c : ℕ}
    {k : GL (Fin 3) (v.adicCompletion K)} (hk : k ∈ congruenceK1 R K v c) :
    k⁻¹ ∈ congruenceK1 R K v c := by sorry
