-- Prove2me | Theorems.Thm_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le
-- name    : ModularForm.exists_katzGamma0Form_evalCusp_eq_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/e4e90d84-18e7-5cd1-948a-b18f15e2d808
-- title:
--   Weight-two Γ₀(p) forms as Katz forms over ℤ[1/p]
-- statement:
--   Let $p$ be a prime with $5 \le p$, let $h$ be a modular form of weight $2$ for $\Gamma_0(p)$ in the analytic sense, and let $b : \mathbb{N} \to \mathbb{Z}$ be such that for every $n$ the complex number $b_n$ is the $n$-th coefficient of the $q$-expansion of $h$ of width $1$. Then there is a Katz $\Gamma_0$-form $\varphi$ of level $p$ and weight $2$ over $\mathbb{Z}[1/p] =$ `Localization.Away (p : ℤ)`, that is: a rule assigning to each $\mathbb{Z}[1/p]$-algebra $A$, each Weierstrass curve $W$ over $A$ with invertible discriminant and each quadruple $D = (x_P,y_P,x_Q,y_Q)$ in $A$ which is a level-$p$ structure (both $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine equation of $W$, both $x_P$ and $x_Q$ are roots of $W$'s $p$-th pre-division polynomial, and the two elements $\mathrm{indepElt}(W,p,x_P,x_Q)$, $\mathrm{indepElt}(W,p,x_Q,x_P)$ are units) an element of $A$, compatible with $\mathbb{Z}[1/p]$-algebra maps, scaling by $u^{-2}$ under a variable change with unit $u$, and unchanged when $P$ is replaced by another point whose $x$-coordinate lies in the same line as $x_Q$, with the following property. For every commutative ring $R$ with a $\mathbb{Z}[1/p]$-algebra structure, every unit $\zeta$ of $R$ satisfying $\sum_{i<p} \zeta^{i} = 0$, and whenever the cusp data $\mathrm{cuspData}\,R\,p\,\zeta\,(1,0)\,(0,1)$ — the pair consisting of the toric point attached to $\zeta$ and the non-toric point attached to $q$ — is a level-$p$ structure on the Tate curve $\mathrm{tateBase}\,R\,p$ over $R((q))$, obtained from the integral Tate curve by the substitution $q \mapsto q^{p}$, the value of $\varphi$ at that curve (with its invertible discriminant) and that cusp data equals the Laurent series associated with the power series $\sum_{n} b_n q^{n}$ with coefficients taken in $R$.
--
--   This is the analytic-to-algebraic passage for weight-two forms on $\Gamma_0(p)$: a classical form with rational integral Fourier coefficients is realised as a Katz-style algebraic modular form over $\mathbb{Z}[1/p]$ whose value at Mazur's cusp of the Tate curve reproduces the given $q$-expansion, in the spirit of Katz's corollary to the $q$-expansion principle and Mazur's comparison of the rings $A$ and $B$ over $\mathbb{Z}[1/p]$. It is used in the arithmetic of $q$-coefficients of such forms, namely by [`ModularForm.dvd_twelve_mul_qCoeff_zero_and_dvd_qCoeff_mul_of_dvd_qCoeff`](thm.html#ModularForm.dvd_twelve_mul_qCoeff_zero_and_dvd_qCoeff_mul_of_dvd_qCoeff) and [`ModularForm.exists_katzModularForm_qExpansion_eq_C_of_dvd_qCoeff`](thm.html#ModularForm.exists_katzModularForm_qExpansion_eq_C_of_dvd_qCoeff); the restriction $5 \le p$ comes from the available criterion making the cusp data a level-$p$ structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_katzGamma0Form_evalCusp_eq_of_five_le.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.exists_katzGamma0Form_evalCusp_eq_of_five_le
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (b : ℕ → ℤ)
    (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n) :
    ∃ φ : ModularCurve.KatzGamma0Form (Localization.Away (p : ℤ)) p 2,
      ∀ (R : Type) [CommRing R] [Algebra (Localization.Away (p : ℤ)) R] (ζ : Rˣ),
        ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0 →
        ∀ hc : ModularCurve.IsLevelPStructure (ModularCurve.tateBase R p) p
            (ModularCurve.cuspData R p ζ ![1, 0] ![0, 1]),
        φ.toKatzLevelPForm.toFun (ModularCurve.tateBase R p) (ModularCurve.isUnit_Δ_tateBase R p) _ hc
          = HahnSeries.ofPowerSeries ℤ R ((PowerSeries.mk b).map (Int.castRingHom R)) := by sorry
