-- Prove2me | Theorems.Thm_FourierDimTesting102_Quantum_Supplement_collision_round_expectation
-- name    : FourierDimTesting102.Quantum.Supplement.collision_round_expectation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:34:22.699721+00:00
-- url     : https://prove2.me/theorems/63bcb3e2-d2e4-4505-b55b-75d5c11911d6
-- title:
--   Lemma 6.3 — one round of Algorithm 4 has $\mathbb E[Z_W]=\frac{\Pr[C_W]}{2}\,\mu_{f,X}(\overline W)$
-- statement:
--   Fix a linear map $X:\mathbb F_2^n\to\mathbb F_2^r$, a $k$-dimensional subspace $W\le\mathbb F_2^r$ with the basis $w_1,\dots,w_k$ used by Algorithm 4, and $\Phi_W(a)=(\langle w_1,a\rangle,\dots,\langle w_k,a\rangle)$. In one round, $x$ is uniform on $\mathbb F_2^n$ and $a_1,\dots,a_\ell$ are independent and uniform on $\mathbb F_2^r$. Let $C_W$ be the event that $\Phi_W(a_i)=\Phi_W(a_j)$ for some $i<j$, and let $Z_W=0$ outside $C_W$ and $Z_W=\mathbf 1[f(x+X^\top a_i)\ne f(x+X^\top a_j)]$ for the lexicographically first such pair on $C_W$. Then
--
--   $$
--   \mathbb E[Z_W]=\frac{\Pr[C_W]}{2}\,\mu_{f,X}(\overline W),\qquad \mu_{f,X}(\overline W)=\sum_{s:\,Xs\notin W}\widehat f(s)^2 .
--   $$
--
--   The estimator $\hat\mu_X(W)$ of Algorithm 4 is therefore unbiased for $\mu_{f,X}(\overline W)$, which the proof of Theorem 6.2 combines with Theorem 6.1.
--
--   Differences from the source:
--   - encoding: boolean functions f : F₂ⁿ → {−1,1} → f is its bit function BoolFn n := (Fin n → ZMod 2) → Bool, with sign toSign f x = (−1)^{f x} (the base Model); reason: a bijection on the same functions; the bit is what the oracle returns
--   - reading: E[Z_W] and Pr[C_W] in one round of Algorithm 4 → the mean over (x, a) uniform on V n × (Fin ℓ → V r) and the probability over a, with X fixed; reason: µ_{f,X} depends on X, so the identity is for the drawn X; the round’s randomness is x_t and a_{t,i}
--   - generalization: ℓ = O(2^{k/2}) points per round and r as in Algorithm 4 → any ℓ and any r; reason: the identity holds for every ℓ and r; Algorithm 4’s values are instances
--   - encoding: an arbitrary basis {w₁, …, w_k} of each W (line 2) → the basis Module.finBasisOfFinrankEq; reason: Φ_W(a) = Φ_W(a′) iff a + a′ ∈ W^⊥ for every basis, so C_W, the chosen pair, Z_W and the output do not depend on the basis
--   - reading: “use an unbiased rule to pick one (e.g., the lexicographically first such pair)” (line 9) → firstCollision, the lexicographically first pair i < j; reason: the source leaves “unbiased” undefined and names this rule as its example; it depends only on the labels Φ_W(a_i), which is what the proof of Lemma 6.3 uses
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.31, Lemma 6.3 (proof pp.31–32)

import Definitions.Def_FourierDimTesting102_Quantum_Supplement_Algorithms

namespace FourierDimTesting102.Quantum.Supplement

open QAlgorithms FourierDimTesting102.Quantum

/-- Lemma 6.3, p.31: fix the linear map `X : F₂ⁿ → F₂ʳ` and a `k`-dimensional subspace `W ≤ F₂ʳ`
with its basis. In one round of Algorithm 4 (`x` uniform on `F₂ⁿ`, `a₁, …, a_ℓ` independent
uniform on `F₂ʳ`, answers `f(x + Xᵀ a_i)`), `E[Z_W] = (Pr[C_W]/2) · μ_{f,X}(W̄)`, where `C_W` is
the event that `Φ_W(a_i) = Φ_W(a_j)` for some `i < j`. -/
theorem collision_round_expectation {n r k ℓ : ℕ} (f : BoolFn n) (X : LinMap n r)
    (W : KSub r k) :
    unifMean (fun xa : V n × (Fin ℓ → V r) =>
        zVal W xa.2 (fun i => f (shiftPt X xa.1 (xa.2 i)))) =
      unifProb (fun a : Fin ℓ → V r => (firstCollision W a).isSome) / 2 *
        massOut (pushforward (fourierDist f) X) W.1 := by sorry

end FourierDimTesting102.Quantum.Supplement
