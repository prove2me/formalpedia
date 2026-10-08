-- Prove2me | Theorems.Thm_HScattered_Bound_result_4_6
-- name    : HScattered.Bound.result_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:20.844344+00:00
-- url     : https://prove2.me/theorems/b1939059-0e33-41ac-86e1-289c94c3646a
-- title:
--   Result 4.6 — Delsarte's Singleton-like bound |C| ≤ q^{m(n − d + 1)} for rank distance codes
-- statement:
--   Let $X$ and $Y$ be $\mathbb F_q$-vector spaces with $\dim_{\mathbb F_q} X = m$ and $\dim_{\mathbb F_q} Y = n$, where $n \le m$. A **rank distance code** of $\mathbb F_q^{n\times m}$ is a set $\mathcal C$ of $\mathbb F_q$-linear maps $X \to Y$, with the **rank distance** $d(f,g) = \operatorname{rk}(f-g)$. Suppose $1 \le d \le n$ and any two distinct elements of $\mathcal C$ have rank distance at least $d$. Then
--
--   $$
--   |\mathcal C| \le q^{\,m(n-d+1)} .
--   $$
--
--   Codes attaining this bound are the maximum rank distance (MRD) codes. The bound is due to Delsarte (1978); in the paper it is the counting step of the case $h = r-1$ of Theorem 2.3.
--
--   **Formalization Note** The paper's hypothesis is that $d$ is the minimum distance $\min\{d(f,g): f,g\in\mathcal C,\ f\ne g\}$. The Lean statement only asks that $d$ be a lower bound for the distances, which implies the minimum-distance version and is how the paper applies it. The range $1 \le d \le n$ (automatic for a minimum distance of a code with two or more elements) keeps $n-d+1$ free of natural-number truncation. $\mathcal C$ is a `Finset` of linear maps, $q$ is `Fintype.card F`, and the rank of $f-g$ is the dimension of its range.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 14, §4.1, Result 4.6, eq. (12) (citing P. Delsarte, Bilinear forms over a finite field, with applications to coding theory, J. Combin. Theory Ser. A 25 (1978))

import Mathlib

namespace HScattered.Bound

/-- Result 4.6 (Delsarte's Singleton-like bound, as stated in arXiv:1906.10590v2, p. 14).
A rank distance code `C` of `𝔽_q^{n×m}`, `n ≤ m`, is a set of `𝔽_q`-linear maps `X → Y` with
`dim X = m`, `dim Y = n`; the distance of `f, g` is `rk(f − g)`. If any two distinct elements of
`C` are at rank distance at least `d` (`1 ≤ d ≤ n`), then `|C| ≤ q^{m(n − d + 1)}`. -/
theorem result_4_6 {F X Y : Type*} [Field F] [Fintype F]
    [AddCommGroup X] [Module F X] [FiniteDimensional F X]
    [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y]
    (m n d : ℕ) (hm : Module.finrank F X = m) (hn : Module.finrank F Y = n) (hnm : n ≤ m)
    (C : Finset (X →ₗ[F] Y)) (hd1 : 1 ≤ d) (hdn : d ≤ n)
    (hC : ∀ f ∈ C, ∀ g ∈ C, f ≠ g → d ≤ Module.finrank F (LinearMap.range (f - g))) :
    C.card ≤ Fintype.card F ^ (m * (n - d + 1)) := by sorry

end HScattered.Bound
