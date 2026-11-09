-- Prove2me | Theorems.Thm_FourierDimTesting102_Quantum_projection_coset_average
-- name    : FourierDimTesting102.Quantum.projection_coset_average
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:00:52.485679+00:00
-- url     : https://prove2.me/theorems/603b5af4-7db9-4526-a638-6d17a254ddde
-- title:
--   Lemma 3.3: the spectral projection is a coset average
-- statement:
--   Let $U$ be a linear subspace of $\mathbb F_2^n$, let $U^\perp$ be its annihilator for the dot product, and let $f$ be a boolean function. For every $x\in\mathbb F_2^n$,
--
--   $$
--   \Pi_Uf(x)=\mathbb E_{h\in U^\perp}[f(x+h)],
--   $$
--
--   where $\Pi_Uf(x)=\sum_{s\in U}\widehat f(s)\chi_s(x)$ and $h$ is uniform on the whole of $U^\perp$, including $0$.
--
--   So the projection of $f$ onto the frequencies in $U$ is the average of $f$ over the coset $x+U^\perp$. This is the bridge between Fourier weight on $U$ and Hamming distance to $C_U$ used in Lemma 3.2.
--
--   Differences from the source:
--   - encoding: boolean functions f : {0,1}^n → {−1,1}, with frequencies written as subsets S ⊆ [n] or their indicator vectors → f is its bit function BoolFn n := (Fin n → ZMod 2) → Bool, with sign toSign f x = (−1)^{f x}, and frequencies are vectors of Fin n → ZMod 2; reason: a bijection on the same functions; the bit is what the XOR oracle adds and the vectors carry the F₂-subspaces
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.15, Lemma 3.3

import Definitions.Def_FourierDimTesting102_Quantum_Model

namespace FourierDimTesting102.Quantum

/-- Lemma 3.3, p.15: `Π_U f(x) = E_{h ∈ U^⊥}[f(x+h)]`, for every subspace `U` and point `x`. -/
theorem projection_coset_average {n : ℕ} (U : Submodule (ZMod 2) (V n)) (f : BoolFn n) (x : V n) :
    proj U f x = cosetAverage U f x := by sorry

end FourierDimTesting102.Quantum
