-- Prove2me | Theorems.Thm_ModularCurve_exists_mul_eval_sub_eval_mem_nonunits_of_mem_gaussValuationSubring_one_mul
-- name    : ModularCurve.exists_mul_eval_sub_eval_mem_nonunits_of_mem_gaussValuationSubring_one_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/6108de0f-36f9-5b62-b955-41197877ed5f
-- title:
--   Residue fields of the two Gauss valuations at level p
-- statement:
--   Let $p$ be a prime and let $F =$ `modularFunctionFieldFull (1 * p)` be the intermediate field of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the series $\mathrm{qExpand}\,\mathbb{Q}\,d\,(jq)$ for the divisors $d$ of $1\cdot p$, i.e.\ by $j(q)$ and $j(q^{p})$. Let $W_0, W_1$ be valuation subrings of $F$ such that: $f \in W_0$ precisely when there are Laurent series $x, y$ over $\mathbb{Z}$ whose coefficientwise reduction of $y$ modulo $p$ is nonzero and with $f \cdot y = x$ after pushing $x, y$ coefficientwise into $\mathbb{Q}((q))$; $f \in W_1$ precisely when $\mathrm{atkinLehnerInvolutionFull}\;1\;p\,(f) \in W_0$, where that automorphism is a chosen $\mathbb{Q}$-algebra automorphism of $F$ interchanging $j(q)$ and $j(q^{p})$ (and the identity if none exists); and $W_0 \neq W_1$. Let $j_p \in F$ have $q$-expansion $\mathrm{qExpand}\,\mathbb{Q}\,p\,(jq)$. The conclusion is twofold: for every $x \in W_0$ there are $P, Q \in \mathbb{Z}[X]$ with $Q$ nonzero modulo $p$ and $x \cdot Q(j) - P(j)$ a non-unit of $W_0$, $j$ being the element $jq$ of $F$; and for every $x \in W_1$ there are such $P, Q$ with $x \cdot Q(j_p) - P(j_p)$ a non-unit of $W_1$. Here the polynomials are evaluated through the structure map $\mathbb{Z} \to F$.
--
--   In valuation-theoretic form this says that the residue field of the Gauss valuation ring $W_0$ of the $q$-expansion is generated over $\mathbb{F}_p$ by the reduction of $j$, and that of its Atkin–Lehner transform $W_1$ by the reduction of $j_p$ — the two irreducible components of the special fibre of $X_0(p)$ at $p$, each a copy of the $j$-line. It is used in the construction of the charts of the Deligne–Rapoport model, through [`ModularCurve.DRModel.exists_chartAlgFin_valuationSubring_pair_levelP`](thm.html#ModularCurve.DRModel.exists_chartAlgFin_valuationSubring_pair_levelP).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mul_eval_sub_eval_mem_nonunits_of_mem_gaussValuationSubring_one_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_AtkinLehnerPartial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_mul_eval_sub_eval_mem_nonunits_of_mem_gaussValuationSubring_one_mul
    (p : ℕ) [Fact p.Prime] [NeZero p]
    (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull (1 * p)))
    (hW₀ : ∀ f : ↥(modularFunctionFieldFull (1 * p)), f ∈ W₀ ↔
      ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
        (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x)
    (hW₁ : ∀ f : ↥(modularFunctionFieldFull (1 * p)), f ∈ W₁ ↔ atkinLehnerInvolutionFull 1 p f ∈ W₀)
    (hne : W₀ ≠ W₁)
    (jp : ↥(modularFunctionFieldFull (1 * p))) (hjp : (jp : LaurentSeries ℚ) = qExpand ℚ p jq) :
    (∀ x : ↥(modularFunctionFieldFull (1 * p)), x ∈ W₀ →
      ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p)))
              ⟨jq, modularFunctionField_le_full (1 * p) (jq_mem (1 * p))⟩ Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p)))
              ⟨jq, modularFunctionField_le_full (1 * p) (jq_mem (1 * p))⟩ P ∈ W₀.nonunits) ∧
    (∀ x : ↥(modularFunctionFieldFull (1 * p)), x ∈ W₁ →
      ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p))) jp Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (1 * p))) jp P ∈ W₁.nonunits) := by sorry
