-- Prove2me | Theorems.Thm_LaurentSeries_heckeV_eq_qExpand
-- name    : LaurentSeries.heckeV_eq_qExpand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/544cfadc-53a0-503c-beb2-051871a077d3
-- title:
--   V_ℓ on Laurent series equals substitution q↦ q^ℓ
-- statement:
--   Let $R$ be a commutative ring, let $\ell$ be a nonzero natural number, and let $f$ be a formal Laurent series over $R$, i.e. an element of `LaurentSeries R` (a Hahn series over $\mathbb{Z}$ with coefficients in $R$ and support bounded below). On one side stands `heckeV R ℓ` applied to the positivity $0 < \ell$ coming from $\ell \neq 0$: by definition this is the $R$-linear map sending $f$ to the Laurent series whose coefficient in degree $n \in \mathbb{Z}$ is $f$'s coefficient in degree $n/\ell$ (integer division) when $\ell \mid n$, and $0$ otherwise, the resulting support being bounded below. On the other side stands `qExpand R ℓ`, the ring homomorphism of `LaurentSeries R` obtained by embedding the index monoid along multiplication by $\ell$ on $\mathbb{Z}$, which is injective and order-preserving because $\ell > 0$; thus it moves the coefficient in degree $n$ to degree $\ell n$ and puts $0$ in degrees not divisible by $\ell$. The assertion is that the two Laurent series agree: $V_{\ell} f = f(q^{\ell})$.
--
--   This identifies the formal Hecke-type operator $V_{\ell}$ on $q$-expansions with the substitution $q \mapsto q^{\ell}$, so that statements proved for the ring homomorphism `qExpand` may be applied to $V_{\ell}$ and conversely. It is used in the analysis of $q$-expansions attached to the modular curve $X_0$, in the comparison of a theta-type expansion in $q$ with the corresponding expansion in $q^{N}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LaurentSeries_heckeV_eq_qExpand.lean

import Mathlib
import Definitions.Def_LaurentSeries_HeckeU
import Definitions.Def_LaurentSeries_HeckeV
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open ModularCurve LaurentSeries

theorem LaurentSeries.heckeV_eq_qExpand (R : Type*) [CommRing R] (ℓ : ℕ) [NeZero ℓ] (f : LaurentSeries R) :
    heckeV R ℓ (Nat.pos_of_ne_zero (NeZero.ne ℓ)) f = qExpand R ℓ f := by sorry
