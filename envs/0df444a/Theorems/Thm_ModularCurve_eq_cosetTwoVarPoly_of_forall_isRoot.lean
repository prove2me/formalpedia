-- Prove2me | Theorems.Thm_ModularCurve_eq_cosetTwoVarPoly_of_forall_isRoot
-- name    : ModularCurve.eq_cosetTwoVarPoly_of_forall_isRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/76b5b667-0974-59be-91d2-52b7881c5c7b
-- title:
--   Uniqueness of the coset factorisation over K((t))
-- statement:
--   Let $K$ be a field, let $N$ be a natural number with $N\neq 0$, and let $\zeta\in K^{\times}$ be a primitive $N$-th root of unity. Let $J\in K((t))$ be a Laurent series whose coefficient in degree $-1$ is nonzero and whose coefficients in all degrees $m<-1$ vanish, i.e. $J$ has a pole of order exactly one. Write [`ModularCurve.primCosetReps N`](def/ModularCurve_PrimCosetReps.html#L8) for the finite set of triples $(a,b,d)$ of natural numbers, each at most $N$, with $ad=N$, $b<d$ and $\gcd(a,\gcd(b,d))=1$; for such a triple, [`ModularCurve.cosetConj ζ J (a,b,d)`](def/ModularCurve_PrimCosetReps.html#L34) is $0$ when $a=0$ and otherwise the image of $J$ under [`ModularCurve.cosetSubst ζ a b`](def/ModularCurve_PhiGen.html#L111), the ring endomorphism of $K((t))$ obtained by the twist by $\zeta^{ab}$ followed by the $q$-expansion operator of index $a^{2}$, so that its coefficient in degree $a^{2}m$ is $\zeta^{abm}$ times the degree-$m$ coefficient of $J$ and its coefficients in degrees not divisible by $a^{2}$ vanish — formally $J(\zeta^{ab}t^{a^{2}})$. Let $P\in K((t))[X]$ be monic with `natDegree` equal to the cardinality of [`ModularCurve.primCosetReps N`](def/ModularCurve_PrimCosetReps.html#L8), and suppose that $P$ vanishes at [`ModularCurve.cosetConj ζ J t`](def/ModularCurve_PrimCosetReps.html#L34) for every $t$ in that set. Then $P$ equals $\prod_{t}\bigl(X-\mathrm{C}(\mathtt{cosetConj}\ \zeta\ J\ t)\bigr)$, the polynomial [`ModularCurve.cosetTwoVarPoly ζ N J`](def/ModularCurve_PrimCosetReps.html#L44).
--
--   This is the uniqueness step in the classical determination of the modular polynomial $\Phi_N$: a monic polynomial of the expected degree annihilating all the conjugates $J(\zeta^{ab}t^{a^{2}})$ must be the product of the corresponding linear factors. It is used in the treatment of $\Phi_N$ over $K((t))$, notably to identify the image of the modular polynomial in the adjoined extension, to obtain separability of its reduction, and in a valuation estimate for the associated coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_cosetTwoVarPoly_of_forall_isRoot.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.eq_cosetTwoVarPoly_of_forall_isRoot (K : Type*) [Field K] (N : ℕ) (hN : N ≠ 0)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ N) (J : LaurentSeries K)
    (hJ : J.coeff (-1) ≠ 0) (hJ' : ∀ m : ℤ, m < -1 → J.coeff m = 0)
    (P : Polynomial (LaurentSeries K)) (hP : P.Monic) (hdeg : P.natDegree = (ModularCurve.primCosetReps N).card)
    (hroot : ∀ t ∈ ModularCurve.primCosetReps N, P.IsRoot (ModularCurve.cosetConj ζ J t)) :
    P = ModularCurve.cosetTwoVarPoly ζ N J := by sorry
