-- Prove2me | Theorems.Thm_ModularCurve_StarBank_count
-- name    : ModularCurve.StarBank.count
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/ae69b4a6-0fc7-551f-af80-2e78508efb87
-- title:
--   Rigidity for G∘ R ∣ c Gᵖ⁺¹ with R monic of degree p
-- statement:
--   Let $K$ be an algebraically closed field and let $p$ be a natural number with $2 \le p$ whose image in $K$ is nonzero (so $\operatorname{char} K \nmid p$; $p$ is not assumed prime). Let $R, G \in K[X]$, with $R$ monic of degree exactly $p$ (`natDegree` $= p$) and $G$ of positive degree, and let $c \in K$ be nonzero. Assume that the composite $G(R(X))$ divides $c \cdot G(X)^{p+1}$ in $K[X]$. Then there is a $\beta_0 \in K$ such that, first, every root $\beta$ of $G$ in $K$ equals $\beta_0$ — that is, $G$ has a single root, necessarily $\beta_0$, so $G$ is a nonzero scalar times $(X-\beta_0)^{\deg G}$ — and, second, $R$ is given exactly by $$R = (X - \beta_0)^p + \beta_0 .$$ The conclusion is an existence statement: the same $\beta_0$ serves both for the root of $G$ and for the normal form of $R$. No hypothesis of separability or of coprimality between $R$ and $G$ is imposed, and the divisibility is required only up to the nonzero constant $c$.
--
--   A purely polynomial rigidity statement: divisibility of $c\,G^{p+1}$ by $G\circ R$ forces $R(X)-R(\beta) = (X-\beta)^p$ at each root $\beta$ of $G$, and comparison of the coefficients of $X^{p-1}$ (which equals $-p\beta$, whence the need for $p$ invertible and $p \ge 2$) shows that two distinct roots cannot coexist. It is used by [`ModularCurve.StarBank.starBank`](thm.html#ModularCurve.StarBank.starBank) in the analysis of correspondences between the $j$-invariant and its Hecke translates, where the hypothesis on $p$ in $K$ excludes the characteristic-$p$ phenomenon $R = X^p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_StarBank_count.lean

import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem ModularCurve.StarBank.count {K : Type*} [Field K] [IsAlgClosed K] {p : ℕ}
    (hp0 : (p : K) ≠ 0) (hp2 : 2 ≤ p) {R G : Polynomial K} (hR : R.Monic)
    (hRdeg : R.natDegree = p) (hG : 0 < G.natDegree) {c : K} (hc : c ≠ 0)
    (hdvd : G.comp R ∣ Polynomial.C c * G ^ (p + 1)) :
    ∃ β₀ : K, (∀ β : K, G.IsRoot β → β = β₀) ∧
      R = (Polynomial.X - Polynomial.C β₀) ^ p + Polynomial.C β₀ := by sorry
