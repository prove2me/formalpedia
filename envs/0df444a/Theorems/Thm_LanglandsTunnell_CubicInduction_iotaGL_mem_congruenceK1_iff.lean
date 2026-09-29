-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_iotaGL_mem_congruenceK1_iff
-- name    : LanglandsTunnell.CubicInduction.iotaGL_mem_congruenceK1_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/2e1695f4-b0f6-53ee-83e5-fd7c4148bad4
-- title:
--   diag(g,1) lies in K₁(𝔭ᶜ) iff integral
-- statement:
--   Let $R$ be a Dedekind domain with field of fractions $K$, let $v$ be a height-one prime of $R$, and let $K_v$ denote the completion of $K$ at $v$, with its valuation $\mathrm{Valued.v}$ taking values in $\mathbb{Z}$-exponentials. Let $c$ be a natural number and let $g \in \mathrm{GL}_2(K_v)$. Write $\iota(g) = \mathrm{diag}(g,1) \in \mathrm{GL}_3(K_v)$ for the image of $g$ under the monoid homomorphism `iotaGL`, which sends a $2\times 2$ invertible matrix $M$ to the $3\times 3$ matrix with $M$ in the upper left block, last row $(0,0,1)$ and last column $(0,0,1)^{t}$. Here `localMaximalCompact3` is the subgroup of $\mathrm{GL}_3(K_v)$ consisting of those $k$ all of whose entries and all of whose entries of $k^{-1}$ have valuation at most $1$, and `congruenceK1 R K v c` is the set of $k$ in this subgroup which further satisfy $\mathrm{v}(k_{20}) \le \exp(-c)$, $\mathrm{v}(k_{21}) \le \exp(-c)$ and $\mathrm{v}(k_{22} - 1) \le \exp(-c)$. The assertion is that $\iota(g)$ lies in `congruenceK1 R K v c` if and only if $\iota(g)$ lies in `localMaximalCompact3 R K v`.
--
--   The set `congruenceK1` is the mirabolic congruence condition of level $\mathfrak p_v^c$ on the bottom row of $\mathrm{GL}_3(K_v)$; the statement records that this condition is vacuous on the image of $\mathrm{GL}_2$ under $g \mapsto \mathrm{diag}(g,1)$, so that membership reduces to integrality of the matrix and of its inverse. It is used in the local analysis of Whittaker data and spherical torus values for the cubic induction, where integrals over $\mathrm{GL}_2$-cells are compared with congruence subgroups of $\mathrm{GL}_3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_iotaGL_mem_congruenceK1_iff.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain

theorem
LanglandsTunnell.CubicInduction.iotaGL_mem_congruenceK1_iff
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (c : ℕ) (g : GL (Fin 2) (v.adicCompletion K)) :
    iotaGL g ∈ congruenceK1 R K v c ↔ iotaGL g ∈ localMaximalCompact3 R K v := by sorry
