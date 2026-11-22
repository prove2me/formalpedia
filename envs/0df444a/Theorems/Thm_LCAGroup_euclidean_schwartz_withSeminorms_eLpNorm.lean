-- Prove2me | Theorems.Thm_LCAGroup_euclidean_schwartz_withSeminorms_eLpNorm
-- name    : LCAGroup.euclidean_schwartz_withSeminorms_eLpNorm
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:00:47.673716+00:00
-- url     : https://prove2.me/theorems/f9ec3b92-967c-4dde-be2a-3d5c23663275
-- title:
--   Example D.1.10.3 — the $L^p$-seminorms $\|x^\alpha\partial^\beta f\|_{L^p(\mathbb R^m)}$, $1\le p<\infty$, define the topology of the Schwartz space $\mathcal S(\mathbb R^m)$
-- statement:
--   **The topology of the Schwartz space $\mathcal S(\mathbb R^m)$ is defined by $L^p$-seminorms** (Example D.1.10.3 of the source, which refers to Kirillov–Gvishiani for the proof).
--
--   Let $m\ge 0$ be an integer and let $\mathcal S(\mathbb R^m)$ be the space of complex-valued Schwartz functions on $\mathbb R^m$ with its usual Fréchet topology, the one defined by the seminorms
--   $$p_{\alpha,\beta}(f)=\sup_{x\in\mathbb R^m}|x^\alpha\partial_x^\beta f(x)|,\qquad \alpha,\beta\in\mathbb N^m,$$
--   where $x^\alpha=\prod_i x_i^{\alpha_i}$ and $\partial^\beta=\prod_i\partial_{x_i}^{\beta_i}$. Fix a real exponent $1\le p<\infty$ and put
--   $$p_{\alpha,\beta,p}(f)=\|x^\alpha\partial_x^\beta f\|_{L^p(\mathbb R^m,dx)}=\Big(\int_{\mathbb R^m}|x^\alpha\partial_x^\beta f(x)|^p\,dx\Big)^{1/p},\qquad \alpha,\beta\in\mathbb N^m,$$
--   with $dx$ the Lebesgue measure.
--
--   **Statement.** For every $f\in\mathcal S(\mathbb R^m)$ and all $\alpha,\beta$ the number $p_{\alpha,\beta,p}(f)$ is finite, each $p_{\alpha,\beta,p}$ is a seminorm on $\mathcal S(\mathbb R^m)$, and the family $\{p_{\alpha,\beta,p}\}_{\alpha,\beta\in\mathbb N^m}$ defines the topology of $\mathcal S(\mathbb R^m)$: the sets
--   $$\{f:\ p_{\alpha_1,\beta_1,p}(f)<\varepsilon,\dots,p_{\alpha_N,\beta_N,p}(f)<\varepsilon\}$$
--   form a basis of neighbourhoods of $0$. Equivalently, every $p_{\alpha,\beta,p}$ is continuous on $\mathcal S(\mathbb R^m)$ and every sup-seminorm $p_{\alpha,\beta}$ is bounded by a constant times a finite sum of the $p_{\alpha',\beta',p}$.
--
--   The case $p=1$ is (D.1.10.7) and the case $1<p<\infty$ is (D.1.10.8) of the source. The result lets one replace uniform estimates by integral ($L^1$ or Hilbert space $L^2$) estimates when working with the Schwartz topology; the source uses it for its coordinate-free $L^q$ description of the topology of $\mathcal S(G)$ for an elementary abelian Lie group $G$ (Proposition D.1.10.6) and for the families of seminorms on $\mathcal S(C_F)$ (Propositions D.1.10.9 and D.1.10.10).
--
--   **Formalization Note.** $\mathcal S(\mathbb R^m)$ is Mathlib's `𝓢(EuclideanSpace ℝ (Fin m), ℂ)`; its topology is defined by the seminorms $\sup_x\|x\|^k\|D^nf(x)\|$, which is the same topology as the one defined by the $p_{\alpha,\beta}$. A partial derivative $\partial^\beta f$ is written as an iterated derivative in a finite sequence of coordinate directions $\sigma\colon\{0,\dots,n-1\}\to\{1,\dots,m\}$, namely $D^nf(x)(e_{\sigma(0)},\dots,e_{\sigma(n-1)})$ (`iteratedFDeriv ℝ n f x` applied to the standard basis vectors `EuclideanSpace.single (σ j) 1`); as $(n,\sigma)$ ranges over all finite sequences one gets exactly the operators $\partial^\beta$, each one several times, which does not change the family of seminorms. The statement asserts the existence of a family `q` of seminorms on the Schwartz space, indexed by pairs $(\alpha,(n,\sigma))$, such that `ENNReal.ofReal (q (α, ⟨n, σ⟩) f)` equals the $L^p$-norm `eLpNorm` of $x\mapsto x^\alpha D^nf(x)(e_\sigma)$ for Lebesgue measure `volume` (this encodes finiteness of the norm and determines `q`), and such that `WithSeminorms q`, Mathlib's predicate saying that the topology is the one defined by the family `q`. The exponent is `p : ℝ≥0∞` with `1 ≤ p` and `p ≠ ⊤`. The case $m=0$ is allowed.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 785, Example D.1.10.3, eqs. (D.1.10.6)–(D.1.10.8); classical reference (as cited in the source): A. A. Kirillov and A. D. Gvishiani, Theorems and Problems in Functional Analysis, Springer-Verlag, 1982, Part I, Ch. IV, Thm. 29, pp. 72–74

import Mathlib

open MeasureTheory
open scoped SchwartzMap ENNReal

set_option autoImplicit false

namespace LCAGroup

theorem euclidean_schwartz_withSeminorms_eLpNorm (m : ℕ) (p : ℝ≥0∞) (hp₁ : 1 ≤ p) (hp : p ≠ ⊤) :
    ∃ q : (Fin m → ℕ) × (Σ n : ℕ, Fin n → Fin m) →
        Seminorm ℂ 𝓢(EuclideanSpace ℝ (Fin m), ℂ),
      (∀ (α : Fin m → ℕ) (n : ℕ) (σ : Fin n → Fin m) (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)),
        ENNReal.ofReal (q (α, ⟨n, σ⟩) f) =
          eLpNorm (fun x : EuclideanSpace ℝ (Fin m) =>
            (∏ i, x i ^ α i) •
              iteratedFDeriv ℝ n (⇑f) x (fun j => EuclideanSpace.single (σ j) (1 : ℝ)))
            p volume) ∧
      WithSeminorms q := by sorry

end LCAGroup
