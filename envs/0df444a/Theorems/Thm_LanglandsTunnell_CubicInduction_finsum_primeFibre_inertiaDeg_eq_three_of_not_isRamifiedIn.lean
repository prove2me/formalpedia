-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_finsum_primeFibre_inertiaDeg_eq_three_of_not_isRamifiedIn
-- name    : LanglandsTunnell.CubicInduction.finsum_primeFibre_inertiaDeg_eq_three_of_not_isRamifiedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/778a5803-1dfc-586d-b6d5-e3be8d5fd57d
-- title:
--   Unramified primes in a cubic field: residue degrees sum to three
-- statement:
--   Let $K$ be a number field, equipped with an algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$ that makes $\mathcal{O}_K$ integral over $\mathcal{O}_{\mathbb{Q}}$, and assume $[K:\mathbb{Q}] = 3$. Let $v$ be a point of the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$, i.e. a nonzero prime ideal $v.\mathrm{asIdeal}$ of $\mathcal{O}_{\mathbb{Q}}$, and suppose that $v$ is not ramified in $K$ in the sense of the project predicate `IsRamifiedIn`: there is no $\mathfrak{P}$ in the fibre $\mathrm{primeFibre}\ \mathbb{Q}\ K\ v$, that is, no height-one prime $\mathfrak{P}$ of $\mathcal{O}_K$ whose contraction to $\mathcal{O}_{\mathbb{Q}}$ equals $v$, with $e(\mathfrak{P}/v) = \mathrm{ramificationIdx}'(v.\mathrm{asIdeal}, \mathfrak{P}.\mathrm{asIdeal}) \neq 1$; equivalently, every prime of $K$ above $v$ has ramification index $1$. The conclusion is that the (unconditional, possibly infinite-support) sum over $\mathfrak{P}$ in this fibre of the inertia degrees $\mathrm{inertiaDeg}'(v.\mathrm{asIdeal}, \mathfrak{P}.\mathrm{asIdeal})$ equals $3$.
--
--   This is the elementary splitting dichotomy for a rational prime unramified in a cubic field: the residue degrees of the primes above it sum to the degree $3$, so the prime either splits completely, or splits as a degree-one and a degree-two prime, or is inert. It is used in the construction of the spherical data and Euler factors attached to an induced representation from a cubic field, where it bounds and enumerates the possible local root configurations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_finsum_primeFibre_inertiaDeg_eq_three_of_not_isRamifiedIn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.finsum_primeFibre_inertiaDeg_eq_three_of_not_isRamifiedIn
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsRamifiedIn K v) :
    ∑ᶠ 𝔓 ∈ primeFibre ℚ K v, v.asIdeal.inertiaDeg' 𝔓.asIdeal = 3 := by sorry
