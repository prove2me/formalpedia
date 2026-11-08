-- Prove2me | Theorems.Thm_MaxCompForest_lemma_3_3
-- name    : MaxCompForest.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:40:59.419914+00:00
-- url     : https://prove2.me/theorems/5df3ce45-b22f-4512-b777-944b18dbe713
-- title:
--   Lemma 3.3 — one global feature perturbation
-- statement:
--   Let $\phi,\psi$ be two feature maps $V\to\mathbb R^r$ with $\sqrt{d_v}\,\|\phi_v-\psi_v\|\le\tau$ for every vertex $v$. For every forest $F$ with at most $k$ edges, let $W_\phi(F)$ and $W_\psi(F)$ be the covariance objectives (3.7) under the two feature assignments and the same multipliers $c_e$ and masses $d_v$. Then
--   $$
--   \big|\log W_\phi(F)-\log W_\psi(F)\big|\le\sqrt2\,k\tau .
--   $$
--   So one global rounding of the features perturbs the score of every forest by a controlled multiplicative factor.
--
--   Differences from the source:
--   - generalization: $\psi$ is the specific rounding (3.15), with $\tau=\varepsilon_0/(100k)$ → any $\phi,\psi$ and any $\tau$ with $\sqrt{d_v}\|\phi_v-\psi_v\|\le\tau$ at every vertex; reason: the proof uses only this bound, and (3.15) is one such pair
--   - generalization: rational feature matrix and rational multipliers on a current quotient, with $E_H(\phi)\le q$ in scope → real features, real multipliers and positive masses, on any loopless multigraph; reason: the proof uses neither rationality nor the energy bound
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma 3.3 and (3.15), p.19

import Mathlib
import Definitions.Def_MaxCompForest_covObj
import Definitions.Def_MaxCompForest_IsForest
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

/-- **Lemma 3.3 (One global feature perturbation)**: for any two feature maps with
`√d_v ‖ϕ_v − ψ_v‖ ≤ τ` at every vertex (the conclusion of (3.15)).
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.19.

**Formalization Note.** Both objectives are positive under these hypotheses, so `Real.log` is the real logarithm. -/
theorem lemma_3_3 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (d : V → ℝ) (hd : ∀ v, 0 < d v) {r : ℕ}
    (φ ψ : V → EuclideanSpace ℝ (Fin r)) (τ : ℝ)
    (hτ : ∀ v, Real.sqrt (d v) * ‖φ v - ψ v‖ ≤ τ) (k : ℕ) (F : Finset E) (hF : IsForest G F)
    (hk : F.card ≤ k) :
    |Real.log (covObj G d φ F) - Real.log (covObj G d ψ F)| ≤ Real.sqrt 2 * k * τ := by sorry

end MaxCompForest
