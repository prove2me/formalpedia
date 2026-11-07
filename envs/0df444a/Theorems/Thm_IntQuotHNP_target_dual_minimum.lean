-- Prove2me | Theorems.Thm_IntQuotHNP_target_dual_minimum
-- name    : IntQuotHNP.target_dual_minimum
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:08.198244+00:00
-- url     : https://prove2.me/theorems/e8465f40-3738-4120-bce6-9ff2b5930114
-- title:
--   §3.3 — the target dual minimum is attained, $\lambda_{\mathrm{target}}\ge1/(pX)$, $1\le Z_{\mathrm{target}}\le X$
-- statement:
--   Let $b$ be linearly independent, let $v\neq0$ be a lattice vector with $\|v\|_2\le pX$, and let $p>0$, $X\ge1$. Then:
--
--   1. some $w\in\Lambda^*$ has $\langle v,w\rangle\ne0$;
--   2. the minimum $\lambda_{\mathrm{target}}$ is attained by such a $w$;
--   3. every $w\in\Lambda^*$ with $\langle v,w\rangle\ne0$ has $1\le|\langle v,w\rangle|\le pX\|w\|_2$;
--   4. $\lambda_{\mathrm{target}}\ge1/(pX)$;
--   5. $1\le Z_{\mathrm{target}}\le X$.
--
--   The paper applies this to $v=v_{\mathrm{tar}}=\Phi(px_1)$, whose norm is $pX$. It caps the size of the search in the worst case.
--
--   Differences from the source:
--   - generalization: v_tar = Φ(px_1), with norm exactly pX, for a lattice built from polynomials, and p, X integers → any linearly independent family, any nonzero lattice vector v with norm at most pX, real p > 0 and X ≥ 1; reason: the paper's argument uses only these properties, and v_tar satisfies them
--   - encoding: min → sInf of the set of norms, together with explicit clauses for nonemptiness and attainment; reason: Lean's infimum of an empty set is 0, so the paper's claim that the minimum exists is stated as a conclusion
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), §3.3, pp.19–20 (PDF pp.20–21)

import Mathlib
import Definitions.Def_IntQuotHNP_DualLattice

open InnerProductSpace

namespace IntQuotHNP

/-- **§3.3: the target dual minimum is attained, `λ_target ≥ 1/(pX)` and `1 ≤ Z_target ≤ X`.**
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), §3.3, pp.19–20 (PDF pp.20–21): "Define λ_target = min{∥w∥₂ : w ∈ Λ∗, ⟨v_tar, w⟩ ≠ 0},
Z_target = max{1, (pλ_target)⁻¹}. The set in this minimum is nonempty … ∥v_tar∥₂ = pX. For any w
in the minimum above, its inner product with v_tar is a nonzero integer. Hence
1 ≤ |⟨v_tar, w⟩| ≤ pX∥w∥₂, λ_target ≥ 1/(pX), 1 ≤ Z_target ≤ X."

Let `b` be linearly independent, `v ≠ 0` a lattice vector with `‖v‖ ≤ pX`, `p > 0`, `X ≥ 1`. Then:
1. some `w ∈ Λ∗` has `⟨v, w⟩ ≠ 0`;
2. the minimum is attained: some such `w` has `‖w‖ = λ_target`;
3. every `w ∈ Λ∗` with `⟨v, w⟩ ≠ 0` has `1 ≤ |⟨v, w⟩| ≤ pX‖w‖`;
4. `λ_target ≥ 1/(pX)`;
5. `1 ≤ Z_target ≤ X`.

**Formalization Note.** The paper's `v_tar = Φ(p x₁)` has `‖v_tar‖ = pX`; the statement assumes only
`‖v‖ ≤ pX`. -/
theorem target_dual_minimum {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → EuclideanSpace ℝ κ)
    (v : EuclideanSpace ℝ κ) (p X : ℝ) (hb : LinearIndependent ℝ b) (hv : v ∈ latticeOf b)
    (hv0 : v ≠ 0) (hp : 0 < p) (hX : 1 ≤ X) (hvn : ‖v‖ ≤ p * X) :
    (∃ w ∈ dualLattice b, ⟪v, w⟫_ℝ ≠ 0) ∧
      (∃ w ∈ dualLattice b, ⟪v, w⟫_ℝ ≠ 0 ∧ ‖w‖ = lambdaTarget b v) ∧
      (∀ w ∈ dualLattice b, ⟪v, w⟫_ℝ ≠ 0 → 1 ≤ |⟪v, w⟫_ℝ| ∧ |⟪v, w⟫_ℝ| ≤ p * X * ‖w‖) ∧
      1 / (p * X) ≤ lambdaTarget b v ∧
      1 ≤ zTarget b v p ∧ zTarget b v p ≤ X := by sorry

end IntQuotHNP
