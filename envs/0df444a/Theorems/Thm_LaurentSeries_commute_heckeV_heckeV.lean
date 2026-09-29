-- Prove2me | Theorems.Thm_LaurentSeries_commute_heckeV_heckeV
-- name    : LaurentSeries.commute_heckeV_heckeV
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/7fb3a028-818f-5bfb-a94a-4d59a949cec7
-- title:
--   V_ℓ and V_{ℓ'} commute on Laurent series
-- statement:
--   Let $R$ be a commutative ring and let $\ell,\ell'$ be natural numbers, with proofs $h_\ell : 0<\ell$ and $h_{\ell'} : 0<\ell'$ of positivity, and assume $\ell$ and $\ell'$ are coprime as natural numbers. For a positive integer $m$, the $R$-linear endomorphism `heckeV R m` of the field-free Laurent series object `LaurentSeries R` (Hahn series over $\mathbb{Z}$ with coefficients in $R$ and support bounded below) is defined coefficientwise by sending $f$ to the series whose $n$-th coefficient is the coefficient of $f$ at $n/m$ when $m \mid n$ in $\mathbb{Z}$, and $0$ otherwise; on $q$-expansions this is $q \mapsto q^{m}$, i.e. $\sum a_n q^n \mapsto \sum a_n q^{mn}$. The conclusion is `Commute (heckeV R ℓ hℓ) (heckeV R ℓ' hℓ')`, that is, these two endomorphisms commute in the endomorphism ring of `LaurentSeries R`: their composites in the two orders agree.
--
--   This is the commutation relation among the degree-raising operators $V_\ell$ acting on $q$-expansions, part of the formal bookkeeping for families of Hecke operators on Laurent-series expansions; it is used in deriving the corresponding commutation statement for the operators `heckeT`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LaurentSeries_commute_heckeV_heckeV.lean

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

theorem LaurentSeries.commute_heckeV_heckeV (R : Type*) [CommRing R] (ℓ ℓ' : ℕ) (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ')
    (h : Nat.Coprime ℓ ℓ') :
    Commute (heckeV R ℓ hℓ) (heckeV R ℓ' hℓ') := by sorry
