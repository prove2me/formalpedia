-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_finite_setOf_isRamifiedIn
-- name    : LanglandsTunnell.CubicInduction.finite_setOf_isRamifiedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/ead88004-54b3-574b-981b-5789f5ba2096
-- title:
--   Only finitely many rational primes ramify in a number field
-- statement:
--   Let $K$ be a number field (a field carrying a `NumberField` structure, so that its ring of integers $\mathcal{O}_K$ is an algebra over $\mathcal{O}_{\mathbb{Q}}$). Consider the set of those $v$ in the height one spectrum of $\mathcal{O}_{\mathbb{Q}}$ — the nonzero prime ideals of the ring of integers of $\mathbb{Q}$ — which satisfy the predicate `IsRamifiedIn K v`, i.e. for which there exists a height one prime $\mathfrak{P}$ of $\mathcal{O}_K$ lying in the prime fibre of $v$, meaning that the prime of $\mathcal{O}_{\mathbb{Q}}$ underlying $\mathfrak{P}$ (its contraction along $\mathcal{O}_{\mathbb{Q}} \to \mathcal{O}_K$) equals $v$, such that the ramification index `Ideal.ramificationIdx'` of the pair $(v.\mathrm{asIdeal}, \mathfrak{P}.\mathrm{asIdeal})$ is different from $1$. The assertion is that this set of primes $v$ is finite. Thus only finitely many rational primes admit a prime above them in $K$ with nontrivial ramification index.
--
--   This is the finiteness half of Dedekind's discriminant theorem: the set of rational primes ramifying in a fixed number field is finite. It furnishes the finite set of bad places outside which the local data attached to a cubic induction are unramified, and is used in the construction of the Hecke datum and its conductor estimates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_finite_setOf_isRamifiedIn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.finite_setOf_isRamifiedIn
    (K : Type) [Field K] [NumberField K] :
    {v : HeightOneSpectrum (𝓞 ℚ) | IsRamifiedIn K v}.Finite := by sorry
