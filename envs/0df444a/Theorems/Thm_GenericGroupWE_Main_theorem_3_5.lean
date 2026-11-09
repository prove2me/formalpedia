-- Prove2me | Theorems.Thm_GenericGroupWE_Main_theorem_3_5
-- name    : GenericGroupWE.Main.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:54.711613+00:00
-- url     : https://prove2.me/theorems/db259b92-2ecb-4629-8fc4-6b70f785bb1f
-- title:
--   Theorem 3.5 — Quantitative generic security
-- statement:
--   There is an absolute positive constant $C$ with the following property. Let $n\ge2$, $m\ge16n$, let $2^m\le p<2^{m+1}$ be prime, and let a linearly independent matrix basis have every nonzero combination of rank at least $R$. Every classical generic adversary making at most $Q$ calls satisfies
--
--   $$\operatorname{Adv}_A\le C(Q+m+k)^2(m^{-R}+p^{-1}).$$
--
--   This holds both for the exact law conditional on successful sampling and for the bounded law including common abort. The adversary may inspect all exposed strings, perform arbitrary local computation, and make arbitrary-string queries. The same constant precedes all parameters.
--
--   Differences from the source:
--   - generalization: a fixed false statement producing the rank-gap space → any matrix family satisfying the same independence and rank assumptions; reason: the generic argument depends only on these algebraic properties
--   - encoding: big-O with an absolute hidden constant → one positive constant C before n,m,p,basis,R,Q and adversary; reason: the quantitative and uniform content of the bound is unchanged
-- source:
--   Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, STOC 2027 submission #47 (PDF built 2026-11-02; SHA-256 0b7f14e2db9bb3e199883ab907f854b7b5884c7c9f3d1e4c306bb71e89b659cb), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf, Theorem 3.5, PDF p. 10 (printed p. 9).

import Definitions.Def_GenericGroupWE_Main_Scheme

namespace GenericGroupWE.Main
open scoped BigOperators

theorem theorem_3_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ), 2 ≤ n → 16*n ≤ m →
      ∀ (p : PrimeOrder), 2^m ≤ p.val → p.val < 2^(m+1) →
      ∀ (B : MatrixBundle m p), LinearIndependent (ZMod p.val) B.matrices →
      ∀ R : ℝ,
        (∀ a : Fin B.k → ZMod p.val, B.combination a ≠ 0 → R ≤ (B.combination a).rank) →
        ∀ (Q : ℕ) (A : Adversary Q) (conditional : Bool) (hm : 0 < m),
          schemeAdvantage B n A conditional hm ≤
            C * (Q + m + B.k : ℝ)^2 * ((m : ℝ)^(-R) + (p.val : ℝ)⁻¹) := by sorry

end GenericGroupWE.Main
