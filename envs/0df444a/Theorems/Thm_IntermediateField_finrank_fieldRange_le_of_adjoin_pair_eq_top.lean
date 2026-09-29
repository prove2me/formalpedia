-- Prove2me | Theorems.Thm_IntermediateField_finrank_fieldRange_le_of_adjoin_pair_eq_top
-- name    : IntermediateField.finrank_fieldRange_le_of_adjoin_pair_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/8fe683a8-57ff-553a-b3e0-3ca138c9888b
-- title:
--   Degree bound for a K-endomorphism of a quadratic extension
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and let $X, Y \in L$ be elements generating $L$ over $K$, in the sense that the intermediate field $K(X,Y)$ of $L/K$ is all of $L$. Let $A, B$ be elements of the intermediate field $K(X)$ such that $Y^2 + AY + B = 0$. Let $\mu, \iota$ be $K$-algebra endomorphisms of $L$ such that $\iota X = X$, such that $\iota Y$ satisfies the same quadratic relation $(\iota Y)^2 + A\,\iota Y + B = 0$, and such that $\iota(\mu Y) \neq \mu Y$. Let $\Phi, \Psi \in K[t]$ and let $d$ be a positive natural number such that $\Phi(X) = \mu(X)\,\Psi(X)$ (evaluation of polynomials at $X$ via the $K$-algebra structure), and such that for every intermediate field $M$ of $L/K$ and every $c \in M$ the polynomial $\Phi - c\,\Psi$, taken over $M$, has degree exactly $d$. The conclusion is that $L$ is finite-dimensional as a module over the intermediate field $\mu(L)$, the range of $\mu$, and that $[L : \mu(L)] \leq d$.
--
--   This is an abstract form of the degree bound for the pullback of functions along an isogeny: a $K$-endomorphism $\mu$ of a quadratic extension $L = K(X,Y)$ of a rational function field has index at most $d$ in $L$, where $d$ controls the degree of $\Phi - c\Psi$ and $\iota$ plays the role of the hyperelliptic involution witnessing that $\mu Y \notin K(X)$. It is applied, via [`WeierstrassCurve.Affine.finrank_fieldRange_mulPull_le`](thm.html#WeierstrassCurve.Affine.finrank_fieldRange_mulPull_le), to multiplication by $n$ on the function field of an elliptic curve with $\Phi, \Psi$ built from division polynomials and $d = n^2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_finrank_fieldRange_le_of_adjoin_pair_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IntermediateField.finrank_fieldRange_le_of_adjoin_pair_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L] (X Y : L) (hgen : IntermediateField.adjoin K {X, Y} = ⊤) (A B : L) (hA : A ∈ IntermediateField.adjoin K {X}) (hB : B ∈ IntermediateField.adjoin K {X}) (hY : Y ^ 2 + A * Y + B = 0) (μ ι : L →ₐ[K] L) (hιX : ι X = X) (hιY : ι Y ^ 2 + A * ι Y + B = 0) (hιμ : ι (μ Y) ≠ μ Y) (Φ Ψ : Polynomial K) {d : ℕ} (hd : 0 < d) (hroot : Polynomial.aeval X Φ = μ X * Polynomial.aeval X Ψ) (hdeg : ∀ (M : IntermediateField K L) (c : M), (Φ.map (algebraMap K M) - Polynomial.C c * Ψ.map (algebraMap K M)).natDegree = d) : FiniteDimensional μ.fieldRange L ∧ Module.finrank μ.fieldRange L ≤ d := by sorry
