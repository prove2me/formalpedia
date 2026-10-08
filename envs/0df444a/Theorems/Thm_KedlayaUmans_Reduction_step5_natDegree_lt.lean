-- Prove2me | Theorems.Thm_KedlayaUmans_Reduction_step5_natDegree_lt
-- name    : KedlayaUmans.Reduction.step5_natDegree_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:52.925122+00:00
-- url     : https://prove2.me/theorems/51252999-e6b7-48d7-b9c7-dd1c84f7e3aa
-- title:
--   Proof of Theorem 3.1, Step 5 — $f'(g_{0,0}(X), \dots, g_{m-1,\ell-1}(X))$ has degree less than $N'$
-- statement:
--   Let $R$ be a commutative ring, $2 \le d_0 < d$, $m, N \ge 1$, $\ell = \lceil \log_{d_0} d \rceil$ and $N' = N m \ell d_0$. Let $f \in R[X_0, \dots, X_{m-1}]$, let $g_0, \dots, g_{m-1} \in R[X]$, and let $h \in R[X]$ have degree at most $N - 1$ and unit leading coefficient. With $f' = \psi_{d_0,\ell}(f)$ and $g_{i,j} = g_i^{d_0^{\,j}} \bmod h$,
--   $$
--   \deg f'\bigl(g_{0,0}(X), \dots, g_{m-1,\ell-1}(X)\bigr) < N' .
--   $$
--
--   This is the parenthetical claim of Step 5: the polynomial to be reconstructed has degree below the number $N'$ of evaluation points, so interpolation from $N'$ values determines it.
--
--   **Formalization Note** Stated with `natDegree`. The paper never considers $m = 0$ or $N = 0$; the hypotheses $m \ge 1$ and $N \ge 1$ are added because $N' = 0$ when $m = 0$, and "degree at most $N - 1$" in natural-number arithmetic would otherwise read "at most $0$" for $N = 0$. The individual-degree bound on $f$ and the degree bounds on the $g_i$ are not needed ($\psi$ always produces individual degrees below $d_0$, and the $g_{i,j}$ are reduced modulo $h$) and are omitted.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 10, proof of Theorem 3.1, Step 5 (parenthetical)

import Mathlib
import Definitions.Def_KedlayaUmans_Reduction_Algorithm

namespace KedlayaUmans.Reduction

open Polynomial

theorem step5_natDegree_lt {R : Type*} [CommRing R] {m d N d₀ : ℕ}
    (hd₀ : 2 ≤ d₀) (hd₀d : d₀ < d) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (f : MvPolynomial (Fin m) R) (g : Fin m → R[X])
    (h : R[X]) (hh : h.natDegree ≤ N - 1) (hlc : IsUnit h.leadingCoeff) :
    (MvPolynomial.aeval (step2 d₀ d g h) (step1 d₀ d f)).natDegree < Nprime N m d₀ d := by sorry

end KedlayaUmans.Reduction
