-- Prove2me | Theorems.Thm_GenericGroupWE_Main_lemma_3_4
-- name    : GenericGroupWE.Main.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:56.042119+00:00
-- url     : https://prove2.me/theorems/f12a3c6a-bc31-4854-92be-d32891ba8c70
-- title:
--   Lemma 3.4 — Fixed linear tests
-- statement:
--   Let $m>0$, let $p\ge m$ be prime, and let $M_1,\ldots,M_k$ be linearly independent $m\times m$ matrices over $\mathbb F_p$. Suppose every nonzero combination has rank at least the real number $R$. Fix coefficients $(\alpha,\beta,\gamma)\in\mathbb F_p\times\mathbb F_p^m\times\mathbb F_p^k$ before the random encryption coordinates are sampled. The exact conditional encryption law satisfies
--
--   $$\Pr[\alpha[1]+\textstyle\sum_i\beta_iX_i+\sum_j\gamma_jY_j=[0]]\le m^{-R}+p^{-1}$$
--
--   for every nonzero coefficient vector and either bit. For message one the bound improves to $p^{-1}$. The zero coefficient vector gives probability one for either bit.
--
--   Differences from the source:
--   - generalization: a false SAT instance, its rank-gap basis, and a supplied prime p>=2^m → any linearly independent matrix family with the same rank lower bound, and p>=m; reason: the proof uses only rank, basis independence and the distinct residues 1,...,m
--   - encoding: finite indexed families, prime-field residues, and an encoded group equality test → Fin-indexed ZMod families and the corresponding scalar equality to zero; reason: zero-based finite carriers preserve the instances, and injectivity of every encoding makes the scalar and group equality events identical, so averaging over the encoding is redundant for this test
-- source:
--   Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, STOC 2027 submission #47 (PDF built 2026-11-02; SHA-256 0b7f14e2db9bb3e199883ab907f854b7b5884c7c9f3d1e4c306bb71e89b659cb), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf, Lemma 3.4, PDF p. 9 (printed p. 8).

import Definitions.Def_GenericGroupWE_Main_Scheme

namespace GenericGroupWE.Main
open scoped BigOperators

theorem lemma_3_4 (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (B : MatrixBundle m p)
    (hp : m ≤ p.val)
    (hlin : LinearIndependent (ZMod p.val) B.matrices) (R : ℝ)
    (hrank : ∀ a : Fin B.k → ZMod p.val, B.combination a ≠ 0 →
      R ≤ (B.combination a).rank)
    (α : ZMod p.val) (β : Fin m → ZMod p.val) (γ : Fin B.k → ZMod p.val) :
    ((α = 0 ∧ β = 0 ∧ γ = 0) → ∀ message,
      fixedTestProbability B hm α β γ message = 1) ∧
    ((¬ (α = 0 ∧ β = 0 ∧ γ = 0)) →
      (∀ message, fixedTestProbability B hm α β γ message ≤
        (m : ℝ)^(-R) + (p.val : ℝ)⁻¹) ∧
      fixedTestProbability B hm α β γ true ≤ (p.val : ℝ)⁻¹) := by sorry

end GenericGroupWE.Main
