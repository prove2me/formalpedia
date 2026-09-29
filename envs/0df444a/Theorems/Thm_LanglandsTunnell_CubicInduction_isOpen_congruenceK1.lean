-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isOpen_congruenceK1
-- name    : LanglandsTunnell.CubicInduction.isOpen_congruenceK1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/89a0ada5-f4c9-5fce-91f3-19a97c2e21cf
-- title:
--   Openness of the congruence set K₁(𝔭ᵥᶜ) in GL₃(Kᵥ)
-- statement:
--   Let $R$ be a commutative ring which is a Dedekind domain, let $K$ be a field equipped with an $R$-algebra structure making it a fraction field of $R$, let $v$ be a point of the height-one spectrum of $R$, and write $K_v$ for the $v$-adic completion of $K$ with its valuation $\mathrm{Valued.v}$ taking values in a multiplicative value group written with `WithZero.exp`. For a natural number $c$, the set `congruenceK1 R K v c` consists of those $k$ in the group $GL_3(K_v)$ of invertible $3\times 3$ matrices over $K_v$ such that, first, $k$ lies in the subgroup `localMaximalCompact3 R K v`, i.e. every entry of the matrix underlying $k$ and every entry of the matrix underlying $k^{-1}$ has valuation at most $1$, and, second, the three bottom-row conditions $\mathrm{v}(k_{2,0})\le \exp(-c)$, $\mathrm{v}(k_{2,1})\le \exp(-c)$ and $\mathrm{v}(k_{2,2}-1)\le \exp(-c)$ hold, indices being taken in `Fin 3`. The theorem asserts that this subset is open in the topology of $GL_3(K_v)$.
--
--   The set in question is the mirabolic congruence set $K_1(\mathfrak{p}_v^c)$ inside the maximal compact-type subgroup of $GL_3(K_v)$: integral matrices with integral inverse whose bottom row is congruent to $(0,0,1)$ modulo $\mathfrak{p}_v^c$. Openness is what is needed to treat it as an open subgroup-like neighbourhood when constructing deeply ramified test vectors, and it is used in the construction of test vectors for local Rankin–Selberg integrals with prescribed central character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isOpen_congruenceK1.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain

theorem
LanglandsTunnell.CubicInduction.isOpen_congruenceK1
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (c : ℕ) :
    IsOpen (congruenceK1 R K v c) := by sorry
