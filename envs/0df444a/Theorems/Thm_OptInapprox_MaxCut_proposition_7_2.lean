-- Prove2me | Theorems.Thm_OptInapprox_MaxCut_proposition_7_2
-- name    : OptInapprox.MaxCut.proposition_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:53.482982+00:00
-- url     : https://prove2.me/theorems/61e77b33-ba13-4752-8d7d-116eb467814b
-- title:
--   Proposition 7.2, p. 16 — Inf_i(f) = Σ_{S∋i} f̂(S)² (5)
-- statement:
--   Let $f:\{-1,1\}^n\to\mathbb R$. Then for every $i\in[n]$,
--   $$\mathrm{Inf}_i(f)=\sum_{S\ni i}\hat f(S)^2,$$
--   where $\mathrm{Inf}_i$ is the influence of Definition 2 (expected variance in the $i$-th coordinate) and $\hat f(S)$ the Fourier coefficients.
--
--   This identity relates influences to low-degree influences (Definition 11): in particular $\mathrm{Inf}_i^{\le k}(f)\le\mathrm{Inf}_i(f)$.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 16, Proposition 7.2, eq. (5)

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Cube

namespace OptInapprox.MaxCut

theorem proposition_7_2 {n : ℕ} (f : (Fin n → Bool) → ℝ) (i : Fin n) :
    influence i f = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S), fourier f S ^ 2 := by sorry

end OptInapprox.MaxCut
