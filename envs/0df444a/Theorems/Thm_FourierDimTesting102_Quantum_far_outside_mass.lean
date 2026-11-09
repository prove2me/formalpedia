-- Prove2me | Theorems.Thm_FourierDimTesting102_Quantum_far_outside_mass
-- name    : FourierDimTesting102.Quantum.far_outside_mass
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:01:48.98233+00:00
-- url     : https://prove2.me/theorems/7e97d84d-0cb0-4300-95a7-efe536b31dd3
-- title:
--   Corollary 3.1: far functions have Fourier mass at least $2\epsilon$ outside every subspace of dimension at most $k$
-- statement:
--   Let $f$ be a boolean function on $\mathbb F_2^n$ with $\operatorname{dist}(f,D_k)\ge\epsilon$, where the distance is the minimum over all functions of Fourier dimension at most $k$. Then for every linear subspace $U\le\mathbb F_2^n$ with $\dim U\le k$,
--
--   $$
--   \operatorname{wt}(\overline U)=\sum_{s\notin U}\widehat f(s)^2\ge2\epsilon.
--   $$
--
--   This holds for all such subspaces at once, so it applies to the span $W$ observed at any point of Algorithm 1: as long as $\dim W\le k$, Fourier sampling finds a string outside $W$ with probability at least $2\epsilon$.
--
--   Differences from the source:
--   - encoding: boolean functions f : {0,1}^n → {−1,1}, with frequencies written as subsets S ⊆ [n] or their indicator vectors → f is its bit function BoolFn n := (Fin n → ZMod 2) → Bool, with sign toSign f x = (−1)^{f x}, and frequencies are vectors of Fin n → ZMod 2; reason: a bijection on the same functions; the bit is what the XOR oracle adds and the vectors carry the F₂-subspaces
--   - generalization: ϵ is the positive farness parameter of Definition 2.5 → ε is any real number; reason: no sign hypothesis is needed for the implication, and positive ε is the source’s case
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.13, Corollary 3.1

import Definitions.Def_FourierDimTesting102_Quantum_Model

namespace FourierDimTesting102.Quantum

/-- Corollary 3.1, p.13: if `dist(f, D_k) ≥ ε`, then `wt(Ū) ≥ 2ε` for all `U` with `dim U ≤ k`. -/
theorem far_outside_mass {n k : ℕ} {ε : ℝ} (f : BoolFn n)
    (hfar : ε ≤ distToSet f (Dk n k)) (U : Submodule (ZMod 2) (V n))
    (hU : Module.finrank (ZMod 2) U ≤ k) :
    2 * ε ≤ wtOut f U := by sorry

end FourierDimTesting102.Quantum
