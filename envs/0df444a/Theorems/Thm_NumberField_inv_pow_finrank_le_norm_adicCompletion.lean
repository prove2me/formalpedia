-- Prove2me | Theorems.Thm_NumberField_inv_pow_finrank_le_norm_adicCompletion
-- name    : NumberField.inv_pow_finrank_le_norm_adicCompletion
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-04T09:28:30.210074+00:00
-- url     : https://prove2.me/theorems/be8ef49b-3747-4470-8420-c7f380830ad8
-- title:
--   A Liouville inequality at a finite place: a non-zero algebraic number of bounded size and denominator is not $v$-adically small
-- statement:
--   Let $L$ be a number field of degree $d = [L : \mathbb{Q}]$, let $v$ be a non-zero prime of $\mathcal{O}_L$, and let $x \in L$, $x \ne 0$. Let $D \ge 1$ be an integer such that $D x$ is an algebraic integer, and let $M$ be a real number with $|\sigma(x)| \le M$ for each embedding $\sigma : L \to \mathbb{C}$. Then
--   $$\|x\|_v \;\ge\; \frac{1}{(D M)^{d}} ,$$
--   where $\|\cdot\|_v$ is the norm of the completion $L_v$, normalized by $\|\pi\|_v = N(v)^{-1}$ for a uniformizer $\pi$.
--
--   **Proof idea.** The number $y = D x$ is a non-zero algebraic integer, so $|N_{L/\mathbb{Q}}(y)| \ge 1$ and $\|y\|_{v'} \le 1$ at each finite place $v'$. The product formula gives $\|y\|_v \ge \prod_{v'} \|y\|_{v'} = |N_{L/\mathbb{Q}}(y)|^{-1}$, and $|N_{L/\mathbb{Q}}(y)| = \prod_\sigma |\sigma(y)| \le (DM)^d$. Finally $\|x\|_v = \|y\|_v / \|D\|_v \ge \|y\|_v$.
--
--   **Use.** In Baker's method the values of the auxiliary function are algebraic numbers of controlled size. This inequality shows that a value that is $v$-adically smaller than the bound is zero. It is the tool for the extrapolation step of Brumer's theorem (`NumberField.Brumer.extrapolation_step`).
--
--   **Formalization Note.** $\|x\|_v$ is `‖algebraMap L (v.adicCompletion L) x‖` with Mathlib's norm on the adic completion of a number field (`NumberField.FinitePlace`); the preamble is `import Mathlib` only. The exponent is $d$ and not $d - 1$, because all embeddings are bounded by $M$. Relevant Mathlib results: `NumberField.FinitePlace.prod_eq_inv_abs_norm_int`, `NumberField.FinitePlace.norm_le_one`, `Algebra.norm_eq_prod_embeddings`.
-- source:
--   Size inequality of transcendence theory: B. Rousseau, Séminaire de Théorie des Nombres de Bordeaux 1968-1969, exposé 11, pp. 4-5 (the definitions of "dénominateur" and "taille" and the inequality before Lemme 2); the archimedean analogue is Lemma 2.7 in S. Dasgupta, Ranks of matrices of logarithms of algebraic numbers I, arXiv:2303.02037. The proof is the product formula.

import Mathlib

open NumberField

theorem NumberField.inv_pow_finrank_le_norm_adicCompletion {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (x : L) (hx : x ≠ 0) (D : ℕ) (hD : 0 < D)
    (hint : IsIntegral ℤ ((D : L) * x)) (M : ℝ) (hM : ∀ σ : L →+* ℂ, ‖σ x‖ ≤ M) :
    (((D : ℝ) * M) ^ Module.finrank ℚ L)⁻¹ ≤ ‖algebraMap L (v.adicCompletion L) x‖ := by sorry
