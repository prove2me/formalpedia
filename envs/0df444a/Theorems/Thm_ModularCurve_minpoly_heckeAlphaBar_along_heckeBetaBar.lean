-- Prove2me | Theorems.Thm_ModularCurve_minpoly_heckeAlphaBar_along_heckeBetaBar
-- name    : ModularCurve.minpoly_heckeAlphaBar_along_heckeBetaBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/40dbcbee-dd91-5773-9f3f-8d2ac21cc71b
-- title:
--   Modular equation as minimal polynomial of α(j) over β
-- statement:
--   Fix a positive integer $N$ and a prime $\ell$ with $\ell \nmid N$, and let $K = \overline{\mathbb{Q}}$. For a level $M$ put $F_M =$ `laurentBaseChange K (modularFunctionFieldFull M)`, the intermediate field of $\mathrm{LaurentSeries}\,K$ obtained by adjoining over $K$ the coefficientwise image (under `coeffEmb`, i.e. $\mathbb{Q} \to K$ applied to coefficients) of the subfield of $\mathrm{LaurentSeries}\,\mathbb{Q}$ generated over $\mathbb{Q}$ by the expansions $\{j(q^{d}) : d \mid M\}$, where $j(q) =$ `jq` is $q^{-1}$ times the power series `jNumQ`. Two $K$-algebra maps $F_N \to F_{N\ell}$ are in play: `heckeAlphaBar`, the inclusion of intermediate fields, and `heckeBetaBar`, the substitution $q \mapsto q^{\ell}$ (multiplication by $\ell$ on Laurent exponents). Let `data` be a `ModularPolynomialData ℓ`, that is a monic $\Phi \in \mathbb{Z}[X][Y]$ with $\deg_Y \Phi = \psi(\ell) = \ell+1$ satisfying the vanishing relation `Φ.eval₂ evalAtJ (jqN ℓ) = 0`, and assume `EvalSymm Φ`: for all Laurent series $x, y$ over $\mathbb{Q}$ one has $\Phi(x, y) = \Phi(y, x)$ in the sense of evaluating the outer variable at $y$ with coefficients evaluated at $x$, and conversely. Then, with $F_{N\ell}$ regarded as an $F_N$-algebra along `heckeBetaBar` (via `algebraAlong`), the minimal polynomial over $F_N$ of the element `heckeAlphaBar` applied to $j \in F_N$ equals $\Phi$ with each coefficient $c \in \mathbb{Z}[X]$ replaced by $c(j) \in F_N$, i.e. $\Phi(j, Y)$.
--
--   This is the classical modular equation read as a minimal polynomial: $j(q)$ is a root of $\Phi_\ell(j(q^{\ell}), Y)$, and since $[F_{N\ell} : \beta(F_N)] = \ell + 1$ when $\ell \nmid N$ ([`ModularCurve.finrankAlong_heckeBetaBar`](thm.html#ModularCurve.finrankAlong_heckeBetaBar)), that root generates the whole extension and its minimal polynomial is the full degree-$(\ell+1)$ polynomial. It underpins the analysis of the two degeneracy maps at level $\ell$, and is cited in the study of fibres and of prolongations of places along `heckeBetaBar` and `heckeAlphaBar`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_minpoly_heckeAlphaBar_along_heckeBetaBar.lean

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.FieldTheory.Minpoly.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.minpoly_heckeAlphaBar_along_heckeBetaBar
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hlN : ¬ ℓ ∣ N)
    (data : ModularPolynomialData ℓ) (hsym : EvalSymm data.Φ) :
    letI := AlgebraicCurve.algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
    minpoly (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ
          ⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩)
      = data.Φ.map (Polynomial.aeval (R := ℤ)
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
            : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))).toRingHom := by sorry
