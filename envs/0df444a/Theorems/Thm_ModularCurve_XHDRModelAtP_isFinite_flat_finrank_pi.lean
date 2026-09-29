-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi
-- name    : ModularCurve.XHDRModelAtP.isFinite_flat_finrank_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/94212206-d7c3-5214-8458-1eb1dde7e59f
-- title:
--   Forgetful map of the model at p is finite flat of rank p+1
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number, let $H$ be a subgroup of $(\mathbb{Z}/M)^{\times}$, and assume $p \mid M$ (`hpM`) but $p^{2} \nmid M$ (`hpM2`), so that $p \parallel M$; assume further that $H$ contains the kernel of the reduction $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$, i.e. every unit $u$ with `ZMod.unitsMap` image $1$ lies in $H$ (`hHp`), and that $M/p \neq 0$. Let `hj` be the hypothesis that the Laurent series `jqModC ℚ`, namely $q^{-1}$ times the integral power series `jNum` $= E_4^{3}\eta^{-24}$ pushed to $\mathbb{Q}$, lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the quotients of integral $q$-expansions of pairs of modular forms of equal weight for $\mathrm{SL}(2,\mathbb{Z})$. Finally let $\mathfrak{X}$ be an inhabitant of the structure `XHDRModelAtP p M H hpM hj`, whose data comprise a proper flat integral normal model of $X_H(M)$ over $\mathbb{Z}_{(p)}$, a smooth proper model at level `ΓN p M H hpM`, a compatible curve model over $\overline{\mathbb{Q}}$ with its Galois equivariance and $q$-expansion pinning, and further fibrewise conditions, together with a morphism $\pi$ from the first model to the scheme `X p (ΓN p M H hpM) hj`. The conclusion asserts that the underlying scheme morphism $\mathfrak{X}.\pi.1$ is finite and locally of finite presentation, that it is flat, and that its rank at every point $x$ of `X p (ΓN p M H hpM) hj` equals $p+1$.
--
--   This is the statement that the forgetful (degeneracy) morphism from the Deligne–Rapoport model of $X_H(M)$ at a prime exactly dividing $M$ down to the model of level $\Gamma_{H'}(M/p)$ is finite locally free of constant degree $p+1$, the degree being the relative degree of the corresponding function fields. It is used in the subsequent analysis of divisors and of the generic and special fibres under this morphism, in particular in the computations of pullbacks of points and of degeneracy relations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard
open scoped MatrixGroups
set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.isFinite_flat_finrank_pi
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) :
    ∃ (_ : IsFinite 𝔛.π.1) (_ : LocallyOfFinitePresentation 𝔛.π.1), Flat 𝔛.π.1 ∧
      ∀ x : ↥(X p (ΓN p M H hpM) hj), 𝔛.π.1.finrank x = p + 1 := by sorry
