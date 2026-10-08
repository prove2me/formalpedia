-- Prove2me | Theorems.Thm_KedlayaUmans_FrobeniusLift_lemma_6_1
-- name    : KedlayaUmans.FrobeniusLift.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:26.513733+00:00
-- url     : https://prove2.me/theorems/9b4d50d0-1f67-4d3d-93bb-e6fd52987492
-- title:
--   Lemma 6.1 — π(f*(φ(α))) = f(α)
-- statement:
--   Let $p$ be a prime and $\mathbb F_q$ a finite field of characteristic $p$. Let $m \ge 0$ and $d \ge 1$, and let $P \in \mathbb F_p[W]$ be irreducible over $\mathbb F_p$ of degree $c$, where $h = p^c$ satisfies $h > m^2 d$. Set
--   $$R = \mathbb F_q[W]/(P(W)), \qquad E(Z) = Z^{h-1} - \eta, \qquad S = R[Z]/(E(Z)),$$
--   where $\eta$ is a primitive element (a generator of the multiplicative group, of order $h-1$) of the field $\mathbb F_p[W]/(P(W)) \subseteq R$. Let $\varphi : \mathbb F_q^m \to S$ be the lift, sending $\alpha$ to the class of the polynomial $g_\alpha$ of degree at most $m-1$ with $g_\alpha(\eta^i) = \sigma^{-i}(\alpha_i)$ ($\sigma : x \mapsto x^h$), and let $\pi : S \to R$ send an element with canonical representative $g(Z)$ (of degree less than $h-1$) to $g(1)$.
--
--   Let $f \in \mathbb F_q[X_0, \dots, X_{m-1}]$ have degree at most $d - 1$ in each variable, and define the univariate polynomial
--   $$f^*(Y) = f\big(Y, Y^h, Y^{h^2}, \dots, Y^{h^{m-1}}\big) \in S[Y].$$
--   Then for every $\alpha \in \mathbb F_q^m \subseteq R^m$,
--   $$\pi\big(f^*(\varphi(\alpha))\big) = f(\alpha).$$
--
--   This is the main lemma of Section 6: multipoint evaluation of the $m$-variate polynomial $f$ over $\mathbb F_q$ reduces to multipoint evaluation of the single univariate polynomial $f^*$ over the ring $S$, followed by the cheap maps $\varphi$ and $\pi$. Theorem 6.2's algebraic algorithm for multivariate multipoint evaluation in small characteristic is this identity applied at every evaluation point.
--
--   **Formalization Note** The paper takes $c$ minimal with $p^c > m^2 d$; the statement is proved for every irreducible $P$ whose degree $c$ satisfies $p^c > m^2 d$, which contains the paper's case. "Individual degrees $d-1$" is read as "at most $d-1$" (`MvPolynomial.degreeOf i f ≤ d - 1` with $d \ge 1$). The objects $R, S, E, \varphi, \pi, f^*$ are those of the two definition files; $\varphi$ is the explicit Lagrange interpolant, and $\pi$ takes the remainder modulo $E$ before evaluating at $1$. Only the identity is formalized: the operation counts of Theorem 6.2 and Corollary 6.3 are not.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 19, Lemma 6.1

import Mathlib
import Definitions.Def_KedlayaUmans_FrobeniusLift_Setup
import Definitions.Def_KedlayaUmans_FrobeniusLift_LiftProject

open Polynomial

namespace KedlayaUmans.FrobeniusLift

/-- Lemma 6.1 (p. 19): for `f ∈ 𝔽_q[X_0, …, X_{m-1}]` with individual degrees at most `d - 1` and every
`α ∈ 𝔽_q^m ⊆ R^m`, `π(f*(φ(α))) = f(α)`. -/
theorem lemma_6_1 (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F] [CharP F p]
    (P : (ZMod p)[X]) [Fact (Irreducible P)]
    (m d : ℕ) (hd : 1 ≤ d) (hmd : m ^ 2 * d < h p P)
    (η : K p P) (hη : IsPrimitiveRoot η (h p P - 1))
    (f : MvPolynomial (Fin m) F) (hf : ∀ i, f.degreeOf i ≤ d - 1) (α : Fin m → F) :
    pi p F P η ((fStar p F P η f).eval (phi p F P η α)) =
      algebraMap F (R p F P) (MvPolynomial.eval α f) := by sorry

end KedlayaUmans.FrobeniusLift
