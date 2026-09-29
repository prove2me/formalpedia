-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_image_pow_mem_nhds_one_units_adicCompletion
-- name    : IsDedekindDomain.HeightOneSpectrum.image_pow_mem_nhds_one_units_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/41e22f90-53cd-5acd-81a7-12eaf8904611
-- title:
--   The n-th power map is open at 1 on Kᵥ^×
-- statement:
--   Let $K$ be a number field (a field of type `Type` carrying a `NumberField` structure), let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$, i.e. an element of `HeightOneSpectrum (𝓞 K)`, and let $K_v =$ `v.adicCompletion K` be the associated $v$-adic completion. Let $n$ be a natural number with $n > 0$, and let $V$ be a subset of the unit group $K_v^\times$ (the Mathlib unit group `(v.adicCompletion K)ˣ`) which is a neighbourhood of $1$ for the topology on $K_v^\times$. The conclusion is that the image of $V$ under the map $s \mapsto s^n$ on $K_v^\times$ is again a neighbourhood of $1$ in $K_v^\times$. Thus the $n$-th power map on the units of a nonarchimedean completion of a number field sends neighbourhoods of $1$ to neighbourhoods of $1$; no claim of injectivity, openness elsewhere, or surjectivity onto a stated set of the form $1 + \mathfrak{p}^m$ is made.
--
--   This is the local statement that $n$-th powers exhaust a neighbourhood of $1$ in $K_v^\times$, the Hensel-type input behind $n$-divisibility of small units in the $v$-adic topology. It is used in the adelic analytic estimates for automorphic forms, where one must adjust an element of $K_v^\times$ by an $n$-th power without leaving a prescribed neighbourhood of the identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_image_pow_mem_nhds_one_units_adicCompletion.lean

import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.image_pow_mem_nhds_one_units_adicCompletion
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : 0 < n)
    (V : Set (v.adicCompletion K)ˣ) (hV : V ∈ nhds (1 : (v.adicCompletion K)ˣ)) :
    (fun s : (v.adicCompletion K)ˣ => s ^ n) '' V ∈ nhds (1 : (v.adicCompletion K)ˣ) := by sorry
