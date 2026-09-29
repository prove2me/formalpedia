-- Prove2me | Theorems.Thm_ModularCurve_heckePic0BarTranspose_fricke_smul
-- name    : ModularCurve.heckePic0BarTranspose_fricke_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/b31c39ff-5650-5309-80e6-a134d25f7eb6
-- title:
--   Fricke automorphism intertwines the Hecke correspondence with its transpose
-- statement:
--   Fix nonzero natural numbers $N$ and $\ell$, and write $\bar F_M$ for `modularFunctionFieldBar M`, the intermediate field of $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ generated over $\overline{\mathbb Q}$ by the coefficientwise image of `modularFunctionFieldFull M`, the latter being $\mathbb Q$ adjoined to the expansions $\mathrm{qExpand}_d(j_q)$ for the nonzero divisors $d$ of $M$. Let $\sigma$ be a $\overline{\mathbb Q}$-algebra automorphism of $\bar F_N$ with the Fricke property `hσ`: whenever $ab=N$ with $a,b$ nonzero and $x\in\bar F_N$ has underlying Laurent series $\mathrm{qExpand}_a(j_q)$ (coefficients embedded into $\overline{\mathbb Q}$), then $\sigma x$ has underlying series $\mathrm{qExpand}_b(j_q)$. Let $\alpha=$ `heckeAlphaBar` be the inclusion $\bar F_N\hookrightarrow\bar F_{N\ell}$ and $\beta=$ `heckeBetaBar` the map $x\mapsto \mathrm{qExpand}_\ell(x)$; both are assumed integral ($h\alpha$, $h\beta$), $\bar F_{N\ell}$ is assumed to have principal divisors of degree zero, and for each of $\alpha$ and $\beta$ the fundamental identity, module-finiteness and the pushforward norm formula along it are assumed. Then for every $x$ in $\mathrm{JZero}\,N=\mathrm{Pic}^0(\overline{\mathbb Q},\bar F_N)$, the transposed correspondence (pullback along $\alpha$ followed by pushforward along $\beta$) applied to $\sigma\cdot x$ equals $\sigma\cdot$ (the correspondence: pullback along $\beta$ followed by pushforward along $\alpha$) applied to $x$, where $\sigma$ acts on divisor classes through `SemilinearAut.ofAlgAut`.
--
--   This is the Atkin–Lehner relation $w_N T_\ell w_N^{-1}=T_\ell^{t}$ on $J_0(N)$ over $\overline{\mathbb Q}$, in the form appropriate to the function-field model of the modular curve, with the Fricke automorphism characterised by its effect on the $q$-expansions $j(q^a)$. It is used in the proof of [`ModularCurve.pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar`](thm.html#ModularCurve.pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar), where the adjointness of Hecke operators with respect to the pairing is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckePic0BarTranspose_fricke_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.heckePic0BarTranspose_fricke_smul (N ℓ : ℕ) [NeZero N] [NeZero ℓ]
    (σ : modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N)
    (hσ : ∀ (a b : ℕ) [NeZero a] [NeZero b], a * b = N →
      ∀ x : modularFunctionFieldBar N,
        (x : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ a jq) →
          ((σ x : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
            = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq))
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))]
    (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ)
    (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ))
    (hNα : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hfinα)
    (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα)
    (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ))
    (hNβ : NormFormulaAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hfinβ)
    (x : JZero N) :
    heckePic0BarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut σ • x)
      = SemilinearAut.ofAlgAut σ • heckePic0Bar hα hβ hFIβ hfinα hNα x := by sorry
