-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_exists_norm_eq_of_inertia_eq_bot
-- name    : IsDedekindDomain.HeightOneSpectrum.Extension.exists_norm_eq_of_inertia_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/ed0258a7-bfef-5747-9013-ae5fee420fd7
-- title:
--   Unramified local units are norms: N(𝒪_w^×)=𝒪ᵥ^×
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra that is Galois over $K$, let $v$ be a height one prime of the ring of integers $\mathcal{O}_K$, and let $w$ be an extension of $v$ to $\mathcal{O}_L$, that is, a height one prime of $\mathcal{O}_L$ whose contraction (`under`) to $\mathcal{O}_K$ is $v$. Assume the inertia subgroup of the prime ideal underlying $w$, taken with respect to the group $L \simeq_{\mathrm{alg}[K]} L$ of $K$-algebra automorphisms of $L$, is trivial. Let $u$ be an element of the $v$-adic completion $K_v$ of $K$ whose valuation $\mathrm{Valued.v}\,u$ equals $1$, i.e. $u$ is a unit of the valuation ring of $K_v$. Then there exists $y$ in the $w$-adic completion $L_w$ of $L$ with valuation $\mathrm{Valued.v}\,y = 1$, again a unit of the valuation ring, whose algebra norm $\mathrm{Algebra.norm}$ relative to the base ring $K_v$ (for the $K_v$-algebra structure on $L_w$) equals $u$.
--
--   This is the local statement that for an unramified extension of local fields the norm map is surjective on the groups of units, equivalently that $\hat H^0$ of the Galois group acting on the units of the valuation ring vanishes, phrased for completions of number fields at a finite place with trivial inertia. It is used when idelic norms are computed place by place, and is cited in the Langlands–Tunnell part of the development and in the local matching of Hecke operators for automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_Extension_exists_norm_eq_of_inertia_eq_bot.lean

import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDedekindDomain.HeightOneSpectrum.Extension.exists_norm_eq_of_inertia_eq_bot
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : v.Extension (NumberField.RingOfIntegers L))
    (hI : w.1.asIdeal.inertia (L ≃ₐ[K] L) = ⊥)
    (u : v.adicCompletion K) (hu : Valued.v u = 1) :
    ∃ y : w.1.adicCompletion L, Valued.v y = 1 ∧ Algebra.norm (v.adicCompletion K) y = u := by sorry
