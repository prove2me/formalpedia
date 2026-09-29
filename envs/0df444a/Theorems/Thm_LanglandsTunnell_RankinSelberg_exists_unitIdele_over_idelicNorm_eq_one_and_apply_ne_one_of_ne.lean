-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unitIdele_over_idelicNorm_eq_one_and_apply_ne_one_of_ne
-- name    : LanglandsTunnell.RankinSelberg.exists_unitIdele_over_idelicNorm_eq_one_and_apply_ne_one_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/bfbf40d1-473b-586c-8303-fd3f9525b4d4
-- title:
--   Norm-one unit idèle nontrivial at a prescribed place above p₀
-- statement:
--   Let $K$ be a number field, let $p_0$ be a height-one prime of the ring of integers $\mathcal O_{\mathbb Q}$, and let $w_0, w_2$ be two elements of `p₀.Extension (𝓞 K)`, i.e. height-one primes of $\mathcal O_K$ whose prime under $\mathcal O_{\mathbb Q}$ is $p_0$, assumed to have distinct underlying primes. Then there exists a unit $u$ of the adèle ring $\mathbb A_K =$ `AdeleRing (𝓞 K) K` (a product of an infinite and a finite part) such that: the infinite component $u_\infty$ equals $1$; the finite component of $u$ at every height-one prime $w$ of $\mathcal O_K$ whose prime under $\mathcal O_{\mathbb Q}$ differs from $p_0$ equals $1$; the valuation of the component of $u$ at every finite place is $1$, so $u$ is a local unit everywhere; the component of $u$ at the prescribed prime $w_0$ is not $1$; and the idelic norm of $u$ for the base change `genuineBaseChange ℚ K` — that is, the image of $u$ under `Units.map` applied to the algebra norm $\mathbb A_K \to \mathbb A_{\mathbb Q}$ taken for the algebra structure coming from the ring homomorphism `genuineβ ℚ K` — equals $1$.
--
--   This is the construction of a non-trivial norm-one unit idèle supported on the places of $K$ above a single rational prime $p_0$, obtained by playing two distinct places above $p_0$ against each other so that the local norms cancel; the hypothesis that two such places exist replaces any degree condition on $K/\mathbb{Q}$. It is used in the assembly of Rankin–Selberg data in the Langlands–Tunnell part of the argument, where such an idèle produces a non-trivial character of the idèle class group trivial away from $p_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_unitIdele_over_idelicNorm_eq_one_and_apply_ne_one_of_ne.lean

import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand.GenuineDescent

theorem LanglandsTunnell.RankinSelberg.exists_unitIdele_over_idelicNorm_eq_one_and_apply_ne_one_of_ne
    (K : Type) [Field K] [NumberField K]
    (p₀ : HeightOneSpectrum (𝓞 ℚ)) (w₀ w₂ : p₀.Extension (𝓞 K)) (hne : w₀.1 ≠ w₂.1) :
    ∃ u : (AdeleRing (𝓞 K) K)ˣ,
      (u : AdeleRing (𝓞 K) K).1 = 1 ∧
      (∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 ℚ) ≠ p₀ →
        ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w = 1) ∧
      (∀ w : HeightOneSpectrum (𝓞 K), Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1) ∧
      ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w₀.1 ≠ 1 ∧
      (genuineBaseChange ℚ K).idelicNorm u = 1 := by sorry
