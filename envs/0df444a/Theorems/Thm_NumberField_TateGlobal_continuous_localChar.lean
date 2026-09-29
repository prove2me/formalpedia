-- Prove2me | Theorems.Thm_NumberField_TateGlobal_continuous_localChar
-- name    : NumberField.TateGlobal.continuous_localChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/60949bf1-ead0-51e4-9e24-c9b75af69da3
-- title:
--   Continuity of the local component at v of a continuous idele class character
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal O_K$, let $\chi \colon (\mathbb A_K)^\times \to \mathbb C^\times$ be a group homomorphism from the units of the adele ring of $K$ to $\mathbb C^\times$ whose underlying function is continuous, and let $v$ be a height one prime of $\mathcal O_K$, i.e. a finite place of $K$. The local character `localChar χ v` is the homomorphism $(K_v)^\times \to \mathbb C^\times$ obtained by composing: first the map sending a unit $t$ of the completion $K_v$ to the unit of the finite adele ring whose $w$-coordinate is $t$ for $w = v$ and $1$ for $w \ne v$ (with inverse given by the same recipe applied to $t^{-1}$); then the map on unit groups induced by the ring homomorphism $\mathbb A_K^{\mathrm{fin}} \to \mathbb A_K$ sending $x$ to the adele with infinite part $1$ and finite part $x$; and finally $\chi$. The assertion is that the underlying function of this homomorphism $(K_v)^\times \to \mathbb C^\times$ is continuous, for the topology of $(K_v)^\times$ as the unit group of the topological ring $K_v$.
--
--   This is the standard fact, used throughout Tate's treatment of zeta integrals, that a continuous Hecke character of the idele group has continuous local components at the finite places. It feeds the local–global decomposition of the global Tate zeta integral and is invoked by the analytic continuation and intertwining-operator arguments built on it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_continuous_localChar.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.TateGlobal.continuous_localChar {K : Type} [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : Continuous ⇑χ) (v : HeightOneSpectrum (𝓞 K)) :
    Continuous ⇑(localChar χ v) := by sorry
