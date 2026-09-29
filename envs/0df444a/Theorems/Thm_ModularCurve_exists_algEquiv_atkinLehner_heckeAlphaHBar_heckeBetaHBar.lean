-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar
-- name    : ModularCurve.exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/0e1ac232-8322-5e59-b707-6fedef5afc35
-- title:
--   Atkin–Lehner automorphism at ℓ exchanging α and β
-- statement:
--   Let $M \ge 1$ (as `NeZero M`), let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, and let $\ell$ be a prime with $\ell \nmid M$. Assume [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113), that is: for every prime $\ell'$ the package `HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ'` holds (it asserts in particular that $q \mapsto q^{\ell'}$ carries `xHFunctionFieldC ℚ M H` into `xHTopFunctionFieldC ℚ M H (M * ℓ')`, together with integrality, principal-divisor, finiteness, fundamental-identity and norm-formula conditions), and for every $d \in (\mathbb{Z}/M)^\times$ there is an $\overline{\mathbb{Q}}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}} \cdot$`xHFunctionFieldC ℚ M H` with `IsDiamondAutHBar M H d σ`. Write $E$ for `laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ))`, the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the field generated over $\mathbb{Q}$ by the ratios of integral $q$-expansions of forms on [`CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)`](def/CohCarrier_Level.html#L133), and $K$ for `xHFunctionFieldBar M H`, the analogous base change of `xHFunctionFieldC ℚ M H`. Then there exists an $\overline{\mathbb{Q}}$-algebra automorphism $w$ of $E$ such that for all $x \in K$ one has $w(\alpha x) = \beta x$ and $w(\beta x) = \alpha(\langle \ell\rangle x)$, where $\alpha =$`heckeAlphaHBar` is the inclusion $K \hookrightarrow E$, $\beta =$`heckeBetaHBar` is the map induced by $q \mapsto q^{\ell}$ when `HeckeBetaHDefined M H ℓ` holds (and is set equal to $\alpha$ otherwise), and $\langle\ell\rangle =$`diamondAutHBar M H` applied to the unit class of $\ell$ in $(\mathbb{Z}/M)^\times$ (a chosen automorphism satisfying `IsDiamondAutHBar`, the identity if none exists). No involutivity of $w$ is asserted.
--
--   This is the Atkin–Lehner automorphism at $\ell$ on the function field of $X_H(M) \cap X_0(\ell)$ over $\overline{\mathbb{Q}}$, in the form of the two commutation relations $w \circ \alpha = \beta$ and $w \circ \beta = \alpha \circ \langle \ell \rangle$ between the two degeneracy maps from level $M$ to level $M\ell$. It is used in the analysis of the $q$-expansion action of Atkin–Lehner, in the reduction of the pair of degeneracy maps modulo $\ell$ and in the construction of regular prolongations of the level-$M\ell$ function field, which together supply the Hecke-correspondence input to the Eichler–Shimura relation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H) :
    ∃ w : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)),
      (∀ x : ModularCurve.xHFunctionFieldBar M H,
          w (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ x) =
            ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ x) ∧
      (∀ x : ModularCurve.xHFunctionFieldBar M H,
          w (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ x) =
            ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ
              (ModularCurve.diamondAutHBar M H
                (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM)) x)) := by sorry
