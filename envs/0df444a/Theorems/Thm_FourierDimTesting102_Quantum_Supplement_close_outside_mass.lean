-- Prove2me | Theorems.Thm_FourierDimTesting102_Quantum_Supplement_close_outside_mass
-- name    : FourierDimTesting102.Quantum.Supplement.close_outside_mass
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:30:30.421532+00:00
-- url     : https://prove2.me/theorems/4a956ff1-6e88-4836-8200-bd75d60504eb
-- title:
--   Lemma 5.1 — a function close to $D_k$ has Fourier mass at most $4\alpha\epsilon$ outside $\operatorname{span}(\operatorname{supp}\hat g)$
-- statement:
--   Let $f,g$ be boolean functions on $\mathbb F_2^n$ with $\operatorname{dist}(f,g)\le\alpha\epsilon$, where $g$ has Fourier dimension at most $k$, and let $U=\operatorname{span}(\operatorname{supp}\widehat g)$. For a string $s$ sampled from the Fourier distribution of $f$ (probability $\widehat f(s)^2$),
--
--   $$
--   \Pr[s\notin U]=\sum_{s\notin U}\widehat f(s)^2\le4\alpha\epsilon .
--   $$
--
--   This is the yes-instance counterpart of Corollary 3.1: functions close to $D_k$ put little Fourier mass outside a fixed subspace of dimension at most $k$. It drives the tolerant testers of Theorems 5.1 and 6.2.
--
--   Differences from the source:
--   - encoding: boolean functions f : F₂ⁿ → {−1,1} → f is its bit function BoolFn n := (Fin n → ZMod 2) → Bool, with sign toSign f x = (−1)^{f x} (the base Model); reason: a bijection on the same functions; the bit is what the oracle returns
--   - encoding: Pr[s ∉ U] for s sampled from the Fourier spectrum of f → wtOut f U = ∑_{s ∉ U} f̂(s)²; reason: the Fourier distribution has weights f̂(s)², a probability distribution by Parseval
--   - generalization: α, ϵ as in Definition 2.6 (0 ≤ α < 1/2, 0 < ϵ < 1/2) → any real α and ε; reason: the implication needs no range; the source’s parameters are a special case
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.23, Lemma 5.1 (proof p.24)

import Definitions.Def_FourierDimTesting102_Quantum_Model

namespace FourierDimTesting102.Quantum.Supplement

open QAlgorithms FourierDimTesting102.Quantum

/-- Lemma 5.1, p.23: if `dist(f, g) ≤ αε`, `g` has Fourier dimension at most `k` and
`U = span(supp ĝ)`, then a Fourier sample `s` of `f` (law `f̂(s)²`) satisfies
`Pr[s ∉ U] = ∑_{s ∉ U} f̂(s)² ≤ 4αε`. -/
theorem close_outside_mass {n k : ℕ} {α ε : ℝ} (f g : BoolFn n) (hfg : boolDist f g ≤ α * ε)
    (hg : fourierDim g ≤ k) : wtOut f (fourierSpan g) ≤ 4 * α * ε := by sorry

end FourierDimTesting102.Quantum.Supplement
