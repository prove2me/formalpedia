-- Prove2me | Theorems.Thm_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent
-- name    : IntermediateField.mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/7dd5bd04-5d4b-5798-9928-7b019886475b
-- title:
--   Field-theoretic Bertini lemma for a generic linear form
-- statement:
--   Let $k$ be an infinite field and $K$ a field extension of $k$ such that the whole of $K$ is finitely generated as an intermediate field of $K/k$, and such that $k$ is separably algebraically closed in $K$: every $\theta \in K$ that is separable algebraic over $k$ lies in the bottom intermediate field, the image of $k$. Fix $n \in \mathbb{N}$, elements $g_0,\dots,g_n \in K$ and scalars $c_0,\dots,c_n \in k$, and work in $\Omega = \operatorname{Frac}\bigl(K[X_0,\dots,X_n]\bigr)$, the fraction field of the polynomial ring in $n+1$ variables over $K$; let $x_i \in \Omega$ be the image of the variable $X_i$. Assume that the $n+3$ elements $x_0,\dots,x_n$, $\xi = \sum_i g_i x_i$ and $\sum_i c_i g_i$ (the latter two taken in $\Omega$ via the structure map of $K$) are algebraically independent over $k$. Then the intermediate field $L = k(x_0,\dots,x_n,\xi)$, obtained by adjoining to $k$ the range of $x$ together with $\xi$, is separably algebraically closed in $\Omega$: every $\theta \in \Omega$ which is separable algebraic over $L$ already lies in $L$.
--
--   This is the field-theoretic core of Jouanolou's proof of the Bertini irreducibility theorem over an infinite ground field, in the formulation where geometric irreducibility of an extension is expressed by separable algebraic closedness of the base in it: the generic member $\xi$ of a linear system over a geometrically irreducible function field again has geometrically irreducible function field. It is used in the proof of [`Ideal.exists_mem_and_mem_and_radical_span_singleton_isPrime`](thm.html#Ideal.exists_mem_and_mem_and_radical_span_singleton_isPrime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem IntermediateField.mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent
    {k : Type u} {K : Type v} [Field k] [Infinite k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG)
    (hsc : ∀ θ : K, IsSeparable k θ → θ ∈ (⊥ : IntermediateField k K))
    {n : ℕ} (g : Fin (n + 1) → K) (c : Fin (n + 1) → k)
    (x : Fin (n + 1) → FractionRing (MvPolynomial (Fin (n + 1)) K))
    (hx : ∀ i, x i = algebraMap (MvPolynomial (Fin (n + 1)) K) _ (MvPolynomial.X i))
    (hind : AlgebraicIndependent k
      (Fin.snoc (Fin.snoc x (∑ i, algebraMap K _ (g i) * x i)) (algebraMap K _ (∑ i, c i • g i))))
    (θ : FractionRing (MvPolynomial (Fin (n + 1)) K))
    (hθ : IsSeparable
      (IntermediateField.adjoin k (Set.range x ∪ {∑ i, algebraMap K _ (g i) * x i})) θ) :
    θ ∈ IntermediateField.adjoin k (Set.range x ∪ {∑ i, algebraMap K _ (g i) * x i}) := by sorry
