-- Prove2me | Theorems.Thm_KedlayaUmans_Reduction_theorem_3_1
-- name    : KedlayaUmans.Reduction.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:49.33518+00:00
-- url     : https://prove2.me/theorems/f60703cb-3e7b-4de9-b6d0-38f30d022bb2
-- title:
--   Theorem 3.1 — the reduction outputs $f(g_0(X), \dots, g_{m-1}(X)) \bmod h(X)$ (correctness)
-- statement:
--   Let $R$ be a commutative ring and $m, N \ge 1$, $2 \le d_0 < d$. Let $f \in R[X_0, \dots, X_{m-1}]$ have individual degrees at most $d - 1$, and let $g_0, \dots, g_{m-1}, h \in R[X]$ have degree at most $N - 1$, with the leading coefficient of $h$ a unit of $R$. Put $\ell = \lceil \log_{d_0} d \rceil$ and $N' = N m \ell d_0$, and let $\beta_0, \dots, \beta_{N'-1}$ be distinct elements of $R$ whose pairwise differences are units. Then the output $r$ of the six-step algorithm of Theorem 3.1 (compute $f' = \psi_{d_0,\ell}(f)$; $g_{i,j} = g_i^{d_0^{\,j}} \bmod h$; $\alpha_{i,j,k} = g_{i,j}(\beta_k)$; the values $f'(\alpha_{\cdot,\cdot,k})$; interpolate them at the $\beta_k$; reduce modulo $h$) is
--   $$
--   r = f\bigl(g_0(X), \dots, g_{m-1}(X)\bigr) \bmod h(X),
--   $$
--   that is, $h \mid f(g_0, \dots, g_{m-1}) - r$ and $\deg r < \deg h$ (or $r = 0$).
--
--   The algorithm uses the multivariate polynomial $f'$ only through its values at the $N'$ points $(\alpha_{0,0,k}, \dots, \alpha_{m-1,\ell-1,k})$, i.e. through one instance of MULTIVARIATE MULTIPOINT EVALUATION with $m\ell$ variables, individual degrees below $d_0$, and $N'$ points. This is the reduction from MODULAR COMPOSITION to MULTIVARIATE MULTIPOINT EVALUATION on which the paper's fast modular-composition and factorization algorithms rest.
--
--   **Formalization Note** Only the correctness half of Theorem 3.1 is formalized; the operation count $O((d^m + mN)d_0)\cdot\mathrm{poly}\log(d^m+mN)$ and the count of invocations are not. The algorithm is the definition `algorithm d₀ d f g h β` (Steps 1–6, written out step for step); $\ell$ is `Nat.clog d₀ d`. "$r = f(g) \bmod h$" is stated by the characterization of the remainder (divisibility plus degree), which determines $r$ uniquely when the leading coefficient of $h$ is a unit; the disjunct $r = 0$ covers the zero ring, where $\deg r < \deg h$ cannot hold as both degrees are $-\infty$. The hypotheses $m \ge 1$ and $N \ge 1$ are added: the paper does not consider $m = 0$ (where $N' = 0$ and nothing can be interpolated) or $N = 0$.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 9, Theorem 3.1, with the algorithm of its proof, pp. 9-10

import Mathlib
import Definitions.Def_KedlayaUmans_Reduction_Algorithm

namespace KedlayaUmans.Reduction

open Polynomial

theorem theorem_3_1 {R : Type*} [CommRing R] {m d N d₀ : ℕ}
    (hd₀ : 2 ≤ d₀) (hd₀d : d₀ < d) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (f : MvPolynomial (Fin m) R) (hf : ∀ i, f.degreeOf i ≤ d - 1)
    (g : Fin m → R[X]) (hg : ∀ i, (g i).natDegree ≤ N - 1)
    (h : R[X]) (hh : h.natDegree ≤ N - 1) (hlc : IsUnit h.leadingCoeff)
    (β : Fin (Nprime N m d₀ d) → R) (hβ : Function.Injective β)
    (hβu : ∀ j k, j ≠ k → IsUnit (β j - β k)) :
    h ∣ MvPolynomial.aeval g f - algorithm d₀ d f g h β ∧
      ((algorithm d₀ d f g h β).degree < h.degree ∨ algorithm d₀ d f g h β = 0) := by sorry

end KedlayaUmans.Reduction
