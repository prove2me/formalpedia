-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isCompact_congruenceK1
-- name    : LanglandsTunnell.CubicInduction.isCompact_congruenceK1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/db1ad97c-8c78-52a7-b8b6-1f34cf261247
-- title:
--   Compactness of the congruence set K₁(mathfrak pᵥᶜ) in GL₃(mathbb Qᵥ)
-- statement:
--   Let $v$ be a height-one prime of the ring of integers $\mathcal O_{\mathbb Q}$ of $\mathbb Q$, let $\mathbb Q_v$ denote the associated adic completion of $\mathbb Q$ with its valuation, and let $c$ be a natural number. The set `congruenceK1` $(\mathcal O_{\mathbb Q}, \mathbb Q, v, c)$ consists of those $k \in GL_3(\mathbb Q_v)$ such that: (i) $k$ lies in the subgroup `localMaximalCompact3`, that is, every entry of the matrix underlying $k$ has valuation $\le 1$ and every entry of the matrix underlying $k^{-1}$ has valuation $\le 1$; and (ii) the bottom row of $k$ satisfies the three valuation bounds $v(k_{2,0}) \le \exp(-c)$, $v(k_{2,1}) \le \exp(-c)$ and $v(k_{2,2} - 1) \le \exp(-c)$, where $\exp(-c)$ denotes the element of the value group $\mathbb Z^{\text{multiplicative}}_{\ge 0}$ corresponding to $-c \in \mathbb Z$. The assertion is that this subset of $GL_3(\mathbb Q_v)$ is compact, $GL_3(\mathbb Q_v)$ carrying its topology as the unit group of the matrix ring over $\mathbb Q_v$. The statement is formulated for the base field $\mathbb Q$ rather than for a general Dedekind domain with fraction field.
--
--   This is the compactness of the mirabolic congruence subset $K_1(\mathfrak p_v^c)$ of $GL_3(\mathbb Q_v)$, the level-$c$ refinement of the compactness of the maximal compact subgroup $GL_3(\mathbb Z_v)$. It is used in the construction of normalised new vectors for local Whittaker data in the cubic-induction and Rankin–Selberg parts of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isCompact_congruenceK1.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.isCompact_congruenceK1 (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℕ) :
    IsCompact (congruenceK1 (𝓞 ℚ) ℚ v c) := by sorry
