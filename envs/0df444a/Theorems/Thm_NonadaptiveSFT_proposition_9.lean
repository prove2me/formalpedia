-- Prove2me | Theorems.Thm_NonadaptiveSFT_proposition_9
-- name    : NonadaptiveSFT.proposition_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:22.195841+00:00
-- url     : https://prove2.me/theorems/591e63cd-f04b-41cc-a840-5dbcb529678d
-- title:
--   Proposition 9 — $\mathbb E_t|h_{v,j,R}|^2=W_{v,j,R}$ and $|\widehat R(f)|\le F_{v,j,R}\le\sqrt{W_{v,j,R}}$ on the node
-- statement:
--   For every $v\in G$, depth $0\le j\le ad$ and signal $R$:
--
--   1. $\mathbb E_t\big[|h_{v,j,R}(t)|^2\big]=W_{v,j,R}$;
--   2. for every $f\in v+H_j$, $|\widehat R(f)|\le F_{v,j,R}\le\sqrt{W_{v,j,R}}$.
--
--   In particular, a node $v+H_j$ containing a coefficient of magnitude at least $T$ has $F_{v,j,R}\ge T$.
--
--   The average magnitude witnesses heavy coefficients (completeness of the locator), while the energy bounds how many nodes can look heavy.
--
--   Differences from the source: none.
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), Proposition 9, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_NonadaptiveSFT_Subgroups

namespace NonadaptiveSFT

/-- **Proposition 9**, p.22 (PDF p.24).

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…).

For any `v`, `j` and `R`:
1. `E_t |h_{v,j,R}(t)|² = W_{v,j,R}`;
2. for any `f ∈ v + H_j`, `|R̂(f)| ≤ F_{v,j,R} ≤ √W_{v,j,R}`.
In particular, a node containing a coefficient of magnitude at least `T` has `F_{v,j,R} ≥ T`.

**Formalization Note.** `j` ranges over the depths `0 ≤ j ≤ ad` of the tree. `E_t` is the uniform
average `(1/N) Σ_t`, `N = 2^{ad}`. The "in particular" clause is stated for every real `T`. -/
theorem proposition_9 (a d : ℕ) (ha : 1 ≤ a) (hd : 1 ≤ d) (v : G a d) (j : ℕ) (hj : j ≤ a * d)
    (R : G a d → ℂ) :
    (1 / (2 : ℝ) ^ (a * d)) * ∑ t, ‖hproj v j R t‖ ^ 2 = Wstat v j R ∧
    (∀ f ∈ coset v j, ‖hat R f‖ ≤ Fstat v j R ∧ Fstat v j R ≤ Real.sqrt (Wstat v j R)) ∧
    (∀ T : ℝ, (∃ f ∈ coset v j, T ≤ ‖hat R f‖) → T ≤ Fstat v j R) := by sorry

end NonadaptiveSFT
