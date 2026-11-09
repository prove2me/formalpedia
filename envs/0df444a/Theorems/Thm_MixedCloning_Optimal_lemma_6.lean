-- Prove2me | Theorems.Thm_MixedCloning_Optimal_lemma_6
-- name    : MixedCloning.Optimal.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:05:20.557596+00:00
-- url     : https://prove2.me/theorems/441d6f32-1b71-4596-b7fe-64b53f0b4fb1
-- title:
--   Lemma 6 — symmetric dimension ratio
-- statement:
--   For integers $n,d\ge1$ and $k\ge0$, write $d[j]=\binom{j+d-1}{j}$ for the dimension of the symmetric $j$-tensor subspace of $\mathbb C^d$. Then
--
--   $$\frac{d[n]}{d[n+k]}\ge1-\frac{kd}{n}.$$
--
--   This controls the loss of global pure-state fidelity when the number of copies is increased by $k$.
--
--   Differences from the source: none.
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 11, Lemma 6

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_6 (n d k : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    1 - (k : ℝ)*d/n ≤ (symDimension d n : ℝ) / symDimension d (n+k) := by sorry

end MixedCloning.Optimal
