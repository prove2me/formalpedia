-- Prove2me | Theorems.Thm_ModularCurve_exists_variableChange_veluQuotient_tateLaurent_eq_and_vcXInv_veluX_toricPoint_eq_of_isPrimitiveRoot
-- name    : ModularCurve.exists_variableChange_veluQuotient_tateLaurent_eq_and_vcXInv_veluX_toricPoint_eq_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/8ba8f891-054e-5b2f-8831-d6f7cd8fa873
-- title:
--   Vélu quotient of the Tate curve by μ_ℓ
-- statement:
--   Let $K$ be a field, $N$ a nonzero natural number, and $\zeta \in K$ a primitive $N$-th root of unity; let $\ell$ be a prime with $\ell \neq 2$ and $\ell \mid N$, and let $m$ be a nonzero natural number. Write $E$ for the Tate curve `tateLaurent K`, the Weierstrass curve over $K((q))$ with $a_1 = 1$, $a_2 = a_3 = 0$ and $a_4, a_6$ the base change of the integral Tate series, and write $E^{(p)} := E$ pushed along the ring endomorphism `qExpand K p` of $K((q))$ that multiplies exponents by $p$ (i.e. the Tate curve with parameter $q^p$). Put $S := \{\,(\text{toricPoint } K\, m\, ((\zeta^{N/\ell})^k) : 1 \le k \le \lfloor \ell/2\rfloor\,\}$, the finite set of toric points of $E^{(m)}$, given by the explicit $q$-expansions of `toricPoint`, attached to the powers of the primitive $\ell$-th root of unity $\zeta^{N/\ell}$; this is one representative from each pair $\{u, u^{-1}\}$ of nontrivial $\ell$-torsion parameters. The assertion is that there is a Weierstrass variable change $C$ over $K((q))$ such that, first, $C$ transforms Vélu's quotient curve $(E^{(m)})^{\mathrm{V}}_S$ — same $a_1, a_2, a_3$, with $a_4$ replaced by $a_4 - 5\sum_{P \in S} t_P$ and $a_6$ by $a_6 - b_2 \sum_{P\in S} t_P - 7\sum_{P \in S} w_P$ — into $E^{(m\ell)}$, and second, for every natural number $n$ with $(\zeta^n)^\ell \neq 1$, Vélu's coordinate functions `veluX`, `veluY` for $S$ applied to the toric point of $E^{(m)}$ with parameter $\zeta^n$, followed by the inverse substitutions $x \mapsto u^{-2}(x - r)$ and $(x,y) \mapsto u^{-3}(y - t - s(x-r))$ of $C$, return exactly the two coordinates of the toric point of $E^{(m\ell)}$ with parameter $(\zeta^n)^\ell$.
--
--   This is the statement that the quotient of the Tate curve with parameter $q^m$ by its toric subgroup $\mu_\ell$ is the Tate curve with parameter $q^{m\ell}$, the isogeny being $u \mapsto u^\ell$ on toric parameters, in the form needed over an arbitrary field containing the $N$-th roots of unity (so of characteristic prime to $N$), with Vélu's explicit constants hidden inside the existential variable change. It is used in the computation of the $j$-invariant of cyclic quotients of the Tate curve at the cusps, in [`ModularCurve.cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples`](thm.html#ModularCurve.cyclicQuotientJ_tateLaurent_baseChange_eq_jqNModC_of_le_zmultiples).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_variableChange_veluQuotient_tateLaurent_eq_and_vcXInv_veluX_toricPoint_eq_of_isPrimitiveRoot.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve
open ModularCurve

universe u

open scoped Classical in

theorem ModularCurve.exists_variableChange_veluQuotient_tateLaurent_eq_and_vcXInv_veluX_toricPoint_eq_of_isPrimitiveRoot
    (K : Type u) [Field K] (N : ℕ) [NeZero N] (ζ : K) (hζ : IsPrimitiveRoot ζ N)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓN : ℓ ∣ N) (m : ℕ) [NeZero m] :
    ∃ C : WeierstrassCurve.VariableChange (LaurentSeries K),
      C • ((tateLaurent K).map (qExpand K m)).veluQuotient
          ((Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K m ((ζ ^ (N / ℓ)) ^ k)) =
        (tateLaurent K).map (qExpand K (m * ℓ)) ∧
      ∀ n : ℕ, (ζ ^ n) ^ ℓ ≠ 1 →
        WeierstrassCurve.Affine.vcXInv C
            (((tateLaurent K).map (qExpand K m)).veluX
              ((Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K m ((ζ ^ (N / ℓ)) ^ k))
              (toricPoint K m (ζ ^ n)).1) =
          (toricPoint K (m * ℓ) ((ζ ^ n) ^ ℓ)).1 ∧
        WeierstrassCurve.Affine.vcYInv C
            (((tateLaurent K).map (qExpand K m)).veluX
              ((Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K m ((ζ ^ (N / ℓ)) ^ k))
              (toricPoint K m (ζ ^ n)).1)
            (((tateLaurent K).map (qExpand K m)).veluY
              ((Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K m ((ζ ^ (N / ℓ)) ^ k))
              (toricPoint K m (ζ ^ n)).1 (toricPoint K m (ζ ^ n)).2) =
          (toricPoint K (m * ℓ) ((ζ ^ n) ^ ℓ)).2 := by sorry
