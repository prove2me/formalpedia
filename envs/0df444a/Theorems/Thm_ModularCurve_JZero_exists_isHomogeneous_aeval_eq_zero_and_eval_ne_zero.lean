-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero
-- name    : ModularCurve.JZero.exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/7ae38b55-a0d0-535a-9763-5691fb4e0ffe
-- title:
--   Separating form vanishing on the model of X₀(N)
-- statement:
--   Let $N$ be a nonzero natural number and let $\bar F_N$ denote `modularFunctionFieldBar N`, the subfield of the Laurent series field over $\overline{\mathbb Q}$ obtained by base change of the field `modularFunctionFieldFull N` along the coefficient embedding. Let $r$ be a natural number and $s \colon \mathrm{Fin}\,r \to \bar F_N$ a family satisfying `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and its $\overline{\mathbb Q}$-span is the Riemann–Roch space $\{f : \mathrm{adicValuation}_w(f) \le \exp((\mathrm{embDivisor}\,N)(w))$ for all places $w\}$ of the divisor `embDivisor N` $= (\mathrm{embDegree}\,N)\cdot[\,\overline\infty\,]$ supported at the cusp at infinity. Let $v \colon \mathrm{Fin}\,r \to \overline{\mathbb Q}$ be a tuple of scalars such that for every place $Q$ of $\bar F_N$ over $\overline{\mathbb Q}$ (a proper valuation subring containing $\overline{\mathbb Q}$ whose ring is a principal ideal ring) and every $c \in \overline{\mathbb Q}$ one has $v \ne c\cdot \mathrm{evalVec}\,s\,Q$, where the $i$-th entry of $\mathrm{evalVec}\,s\,Q$ is the residue at $Q$ of $s_i \cdot s_{j}^{-1}$ with $j$ the pivot index, an index minimising the order at $Q$ among the $s_j$ (and $0$ when $r = 0$). Then there exist $k \in \mathbb N$ and $\Phi \in \overline{\mathbb Q}[X_0,\dots,X_{r-1}]$ homogeneous of degree $k$ with $\Phi(s_0,\dots,s_{r-1}) = 0$ in $\bar F_N$ and $\Phi(v) \ne 0$.
--
--   This is the separating-form step for the projective model of $X_0(N)$ given by a basis of the Riemann–Roch space of the embedding divisor: a tuple of scalars lying on no coordinate row of a place is cut out from the model by a homogeneous form in the ideal of the model. Note that taking $c = 0$ in the hypothesis already forces $v \ne 0$. It is used in [`ModularCurve.exists_log_absValue_evalAt_ge_of_forall_prox_le`](thm.html#ModularCurve.exists_log_absValue_evalAt_ge_of_forall_prox_le) in the height-theoretic analysis of points of $X_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (v : Fin r → AlgebraicClosure ℚ)
    (hv : ∀ (Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (c : AlgebraicClosure ℚ),
      v ≠ c • evalVec s Q) :
    ∃ (k : ℕ) (Φ : MvPolynomial (Fin r) (AlgebraicClosure ℚ)),
      Φ.IsHomogeneous k ∧ MvPolynomial.aeval s Φ = 0 ∧ MvPolynomial.eval v Φ ≠ 0 := by sorry
