-- Prove2me | Theorems.Thm_ModularCurve_variableChange_veluQuotient_tateLaurent_cyclotomicUniv_eq_and_vcXInvR_veluXR_tateToricPoint_eq
-- name    : ModularCurve.variableChange_veluQuotient_tateLaurent_cyclotomicUniv_eq_and_vcXInvR_veluXR_tateToricPoint_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/9297f37a-3002-5593-ad28-4fe16c7ac37e
-- title:
--   Universal Vélu quotient of the Tate curve by μ_ℓ
-- statement:
--   Fix $N\ge 1$, an odd prime $\ell$ dividing $N$, and $m\ge 1$, and work over the Laurent series ring $\mathrm{LaurentSeries}\,(\mathtt{CyclotomicUniv.base}\,N)$, where [`CyclotomicUniv.base N`](def/CyclotomicUniv_Base.html#L19) is the localisation `Localization.Away (den N)`; write $\zeta$ for the unit [`CyclotomicUniv.ζUnit N`](def/CyclotomicUniv_Base.html#L102) and $\ell^{-1}$ for [`CyclotomicUniv.invNat N ℓ hℓN`](def/CyclotomicUniv_Base.html#L108), the inverse of the unit $(\ell)$ of that ring. Let $C=(u,r,s,t)$ be a Weierstrass variable change over $\mathrm{LaurentSeries}$ with $u=\ell$, and with $r$, $s$, $t$ the constant series attached to $\ell^{-1}\cdot\overline{(\ell^2-1)\ell/12}$, $\overline{(\ell-1)/2}$ and $-\ell^{-1}\cdot\overline{(\ell^2-1)\ell/24}$ respectively, the bars denoting natural-number division followed by the cast into the base ring. Let $E_{q^m}$ be the Tate curve `tateLaurent` pushed along the exponent-scaling endomorphism `qExpand _ m` (so $q\mapsto q^m$), and let $S$ be the image of $\{1,\dots,\lfloor\ell/2\rfloor\}$ under $k\mapsto$ `tateToricPoint _ m ((ζ^(N/ℓ))^k)`, the explicit pair of Laurent series, given by divisor sums, of coordinates of the toric point with parameter $\zeta^{kN/\ell}$. The conclusion is twofold. First, applying $C$ to the Vélu quotient of $E_{q^m}$ at $S$ (same $a_1,a_2,a_3$, with $a_4-5\,\mathrm{veluTSum}\,S$ and $a_6-b_2\,\mathrm{veluTSum}\,S-7\,\mathrm{veluWSum}\,S$) gives exactly $E_{q^{m\ell}}$. Secondly, for every $n$ with $N\nmid n\ell$, setting $(x,y)=$ `tateToricPoint _ m (ζ^n)` and $X=\mathrm{veluXR}\,(x)$, $Y=\mathrm{veluYR}\,(x,y)$ for the same $S$ (Vélu's formulas written with `Ring.inverse`), one has $u^{-2}(X-r)$ and $u^{-3}(Y-t-s(X-r))$ equal to the first and second coordinates of `tateToricPoint _ (m*ℓ) ((ζ^n)^ℓ)`.
--
--   This is the integral, universal form of Tate's description of the quotient of the Tate curve $E_{q^m}$ by the subgroup $\mu_\ell$ of its toric points: after the normalising variable change with $u=\ell$ the Vélu quotient is the Tate curve $E_{q^{m\ell}}$, and on toric points the isogeny is $u\mapsto u^{\ell}$. Stated over [`CyclotomicUniv.base N`](def/CyclotomicUniv_Base.html#L19) it specialises to arbitrary base rings carrying a primitive $N$-th root of unity, and it is used by [`ModularCurve.exists_variableChange_veluQuotient_tateLaurent_eq_and_vcXInv_veluX_toricPoint_eq_of_isPrimitiveRoot`](thm.html#ModularCurve.exists_variableChange_veluQuotient_tateLaurent_eq_and_vcXInv_veluX_toricPoint_eq_of_isPrimitiveRoot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_variableChange_veluQuotient_tateLaurent_cyclotomicUniv_eq_and_vcXInvR_veluXR_tateToricPoint_eq.lean

import Mathlib
import Definitions.Def_CyclotomicUniv_Base
import Definitions.Def_ModularCurve_TateVeluRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve CyclotomicUniv ModularCurve.TateVeluRing
open ModularCurve

open scoped Classical in

theorem ModularCurve.variableChange_veluQuotient_tateLaurent_cyclotomicUniv_eq_and_vcXInvR_veluXR_tateToricPoint_eq
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓN : ℓ ∣ N) (m : ℕ) [NeZero m]
    (C : WeierstrassCurve.VariableChange (LaurentSeries (CyclotomicUniv.base N)))
    (hu : (C.u : LaurentSeries (CyclotomicUniv.base N)) = (ℓ : LaurentSeries (CyclotomicUniv.base N)))
    (hr : C.r = HahnSeries.C (CyclotomicUniv.invNat N ℓ hℓN * (((ℓ ^ 2 - 1) * ℓ / 12 : ℕ) : CyclotomicUniv.base N)))
    (hs : C.s = HahnSeries.C (((ℓ - 1) / 2 : ℕ) : CyclotomicUniv.base N))
    (ht : C.t = HahnSeries.C (-(CyclotomicUniv.invNat N ℓ hℓN *
      (((ℓ ^ 2 - 1) * ℓ / 24 : ℕ) : CyclotomicUniv.base N)))) :
    C • ((tateLaurent (CyclotomicUniv.base N)).map (qExpand (CyclotomicUniv.base N) m)).veluQuotient
        ((Finset.Icc 1 (ℓ / 2)).image fun k =>
          tateToricPoint (CyclotomicUniv.base N) m ((CyclotomicUniv.ζUnit N ^ (N / ℓ)) ^ k)) =
      (tateLaurent (CyclotomicUniv.base N)).map (qExpand (CyclotomicUniv.base N) (m * ℓ)) ∧
    ∀ n : ℕ, ¬ N ∣ n * ℓ →
      ModularCurve.TateVeluRing.vcXInvR C
          (ModularCurve.TateVeluRing.veluXR ((tateLaurent (CyclotomicUniv.base N)).map (qExpand (CyclotomicUniv.base N) m))
            ((Finset.Icc 1 (ℓ / 2)).image fun k =>
              tateToricPoint (CyclotomicUniv.base N) m ((CyclotomicUniv.ζUnit N ^ (N / ℓ)) ^ k))
            (tateToricPoint (CyclotomicUniv.base N) m (CyclotomicUniv.ζUnit N ^ n)).1) =
        (tateToricPoint (CyclotomicUniv.base N) (m * ℓ) ((CyclotomicUniv.ζUnit N ^ n) ^ ℓ)).1 ∧
      ModularCurve.TateVeluRing.vcYInvR C
          (ModularCurve.TateVeluRing.veluXR ((tateLaurent (CyclotomicUniv.base N)).map (qExpand (CyclotomicUniv.base N) m))
            ((Finset.Icc 1 (ℓ / 2)).image fun k =>
              tateToricPoint (CyclotomicUniv.base N) m ((CyclotomicUniv.ζUnit N ^ (N / ℓ)) ^ k))
            (tateToricPoint (CyclotomicUniv.base N) m (CyclotomicUniv.ζUnit N ^ n)).1)
          (ModularCurve.TateVeluRing.veluYR ((tateLaurent (CyclotomicUniv.base N)).map (qExpand (CyclotomicUniv.base N) m))
            ((Finset.Icc 1 (ℓ / 2)).image fun k =>
              tateToricPoint (CyclotomicUniv.base N) m ((CyclotomicUniv.ζUnit N ^ (N / ℓ)) ^ k))
            (tateToricPoint (CyclotomicUniv.base N) m (CyclotomicUniv.ζUnit N ^ n)).1
            (tateToricPoint (CyclotomicUniv.base N) m (CyclotomicUniv.ζUnit N ^ n)).2) =
        (tateToricPoint (CyclotomicUniv.base N) (m * ℓ) ((CyclotomicUniv.ζUnit N ^ n) ^ ℓ)).2 := by sorry
