-- Prove2me | Theorems.Thm_FourierDimTesting102_Quantum_distance_le_outside_mass
-- name    : FourierDimTesting102.Quantum.distance_le_outside_mass
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:01:09.766277+00:00
-- url     : https://prove2.me/theorems/f3d29a1d-1c94-4db1-8fd8-107b2c1557f8
-- title:
--   Lemma 3.2: twice the distance to $C_U$ is at most the Fourier mass outside $U$
-- statement:
--   Let $f$ be a boolean function on $\mathbb F_2^n$ and let $U$ be any linear subspace of $\mathbb F_2^n$. Let $\delta_U(f)=\operatorname{dist}(f,C_U)$ be the minimum Hamming distance from $f$ to a boolean function with Fourier support in $U$, and let $\operatorname{wt}(\overline U)=\sum_{s\notin U}\widehat f(s)^2$. Then
--
--   $$
--   2\delta_U(f)\le\operatorname{wt}(\overline U).
--   $$
--
--   So a function far from every boolean function supported on $U$ has substantial Fourier mass outside $U$. This inequality yields Corollary 3.1.
--
--   Differences from the source:
--   - encoding: boolean functions f : {0,1}^n → {−1,1}, with frequencies written as subsets S ⊆ [n] or their indicator vectors → f is its bit function BoolFn n := (Fin n → ZMod 2) → Bool, with sign toSign f x = (−1)^{f x}, and frequencies are vectors of Fin n → ZMod 2; reason: a bijection on the same functions; the bit is what the XOR oracle adds and the vectors carry the F₂-subspaces
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.13, Lemma 3.2 (proof pp.15–16)

import Definitions.Def_FourierDimTesting102_Quantum_Model

namespace FourierDimTesting102.Quantum

/-- Lemma 3.2, p.13: for any subspace `U`, `2 δ_U(f) ≤ wt(Ū)`. -/
theorem distance_le_outside_mass {n : ℕ} (U : Submodule (ZMod 2) (V n)) (f : BoolFn n) :
    2 * deltaU U f ≤ wtOut f U := by sorry

end FourierDimTesting102.Quantum
