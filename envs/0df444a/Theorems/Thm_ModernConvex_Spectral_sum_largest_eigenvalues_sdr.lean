-- Prove2me | Theorems.Thm_ModernConvex_Spectral_sum_largest_eigenvalues_sdr
-- name    : ModernConvex.Spectral.sum_largest_eigenvalues_sdr
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:31.815566+00:00
-- url     : https://prove2.me/theorems/9d121e76-d5c3-44db-b770-977566926fd6
-- title:
--   18.c — the SDR (4.2.2) of the sum of the k largest eigenvalues
-- statement:
--   Let $X$ be a symmetric $m\times m$ matrix and let $k \le m$. Write $S_k(X) = \lambda_1(X) + \cdots + \lambda_k(X)$ for the sum of its $k$ largest eigenvalues, counted with multiplicity. Then for every real $t$,
--   $$S_k(X) \le t \iff \exists\, s \in \mathbb R,\ Z \in \mathbf S^m:\quad \begin{cases} t - ks - \operatorname{Tr}(Z) \ge 0,\\ Z \succeq 0,\\ Z - X + sI_m \succeq 0.\end{cases}$$
--   This is (4.2.2).
--
--   The epigraph of $S_k$ is therefore the projection of the solution set of a system of linear matrix inequalities in $(X,t,s,Z)$, which makes $S_k$ semidefinite representable. The book uses this representation as the building block of Proposition 4.2.1 for every symmetric SDr function of the eigenvalues.
--
--   **Formalization Note** The book writes the epigraph as $\{(X,t) \mid S_k(x) \le t\}$; the lower-case $x$ is a typo for $X$. The semidefinite representability claim is formalized as this explicit equivalence for every symmetric $X$ and real $t$. $Z \in \mathbf S^m$ is implied by $Z \succeq 0$, since Mathlib's `PosSemidef` includes symmetry. $k = 0$ is allowed, as on the page ("$k \le m$").
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 147, example 18.c, Eq. (4.2.2)

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR

open Matrix

namespace ModernConvex.Spectral

/-- Ben-Tal–Nemirovski, example 18.c, p. 147: for a symmetric `m × m` matrix `X` and `k ≤ m`,
the epigraph `{(X, t) | S_k(X) ≤ t}` of the sum of the `k` largest eigenvalues admits the SDR
(4.2.2): `S_k(X) ≤ t` iff there are `s ∈ ℝ` and `Z ∈ Sᵐ` with
(a) `t − ks − Tr(Z) ≥ 0`, (b) `Z ⪰ 0`, (c) `Z − X + sI_m ⪰ 0`. -/
theorem sum_largest_eigenvalues_sdr {m k : ℕ} (hk : k ≤ m) (X : Matrix (Fin m) (Fin m) ℝ)
    (hX : X.IsHermitian) (t : ℝ) :
    sumLargestEig k X ≤ t ↔
      ∃ (s : ℝ) (Z : Matrix (Fin m) (Fin m) ℝ),
        0 ≤ t - (k : ℝ) * s - Z.trace ∧ Z.PosSemidef ∧ (Z - X + s • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef := by sorry

end ModernConvex.Spectral
