-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isOpen_localMaximalCompact3
-- name    : LanglandsTunnell.CubicInduction.isOpen_localMaximalCompact3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/c12111cb-a02a-5d27-824b-987971c97441
-- title:
--   Openness of the integral subgroup of GL₃(Kᵥ)
-- statement:
--   Let $R$ be a Dedekind domain, $K$ a field which is a fraction field of $R$ (given as an $R$-algebra with the fraction-ring property), and let $v$ be a point of the height-one spectrum of $R$, i.e. a non-zero prime ideal of $R$. Write $K_v$ for the $v$-adic completion of $K$, a valued field, and consider the group $\mathrm{GL}_3(K_v)$ of units of the ring of $3\times 3$ matrices over $K_v$ with its topology as a unit group. The subgroup `localMaximalCompact3` consists of those $k \in \mathrm{GL}_3(K_v)$ such that every entry of the matrix underlying $k$ has valuation at most $1$ and every entry of the matrix underlying $k^{-1}$ has valuation at most $1$; it is a subgroup because the unit matrix has integral entries, products of integral matrices are integral, and the defining condition is symmetric in $k$ and $k^{-1}$. The assertion is that the underlying set of this subgroup is an open subset of $\mathrm{GL}_3(K_v)$.
--
--   This is the statement that $\mathrm{GL}_3(\mathcal{O}_v)$, realised as the matrices integral together with their inverses, is an open subgroup of $\mathrm{GL}_3(K_v)$; it is the topological companion of the compactness of the same subgroup. Openness is what is used downstream, for instance to produce a finite set of test vectors spanning the relevant span from an open-subgroup hypothesis, and in the local computations with cyclic subspaces and local zeta factors at the bad places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isOpen_localMaximalCompact3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain

theorem
LanglandsTunnell.CubicInduction.isOpen_localMaximalCompact3
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) :
    IsOpen ((localMaximalCompact3 R K v : Subgroup (GL (Fin 3) (v.adicCompletion K))) :
      Set (GL (Fin 3) (v.adicCompletion K))) := by sorry
