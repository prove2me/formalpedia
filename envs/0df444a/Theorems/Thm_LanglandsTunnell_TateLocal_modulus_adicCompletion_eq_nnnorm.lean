-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
-- name    : LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/149a08bb-c7bd-57cb-8b7b-0977640b2158
-- title:
--   Haar modulus equals the v-adic norm on Kᵥ
-- statement:
--   Let $K$ be a number field, let $v$ be a height-one prime of its ring of integers $\mathcal{O}_K$ (a finite place), and let $x$ be an element of the completion $K_v$ of $K$ at $v$, formed as `IsDedekindDomain.HeightOneSpectrum.adicCompletion`. Write $\mathrm{modulus}$ for the function on a field defined by $\mathrm{modulus}(a) = 0$ when $a = 0$ and, otherwise, $\mathrm{modulus}(a) = \mathrm{distribHaarChar}\,(a)$, the value at the unit determined by $a$ of Mathlib's distributive Haar character, i.e. the nonnegative real factor by which an additive Haar measure on the field scales under the scaling action $S \mapsto aS$. The assertion is that for every $x \in K_v$ this modulus coincides with the nonnegative norm $\lVert x\rVert_+$ carried by $K_v$ as a normed field, the normalised $v$-adic absolute value: an equality of elements of $\mathbb{R}_{\geq 0}$. In particular the case $x = 0$ is included, both sides then being $0$, and on $K_v^\times$ the Haar scaling factor of multiplication by $x$ is $\lVert x\rVert_+$, so that a uniformiser at $v$ has modulus the reciprocal of the absolute norm of $v$ and units of the valuation ring have modulus $1$.
--
--   This is the non-archimedean, finite-place case of the classical identification of the module of an automorphism of a locally compact field (Weil, Tate) with the normalised absolute value, the companion of the real, complex and $p$-adic cases. It is the local normalisation used throughout the local zeta-integral and orbital-integral computations over $K_v$, which invoke it to convert Haar-measure scaling factors into $v$-adic norms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm.lean

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm (K : Type) [Field K]
    [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) :
    modulus x = ‖x‖₊ := by sorry
