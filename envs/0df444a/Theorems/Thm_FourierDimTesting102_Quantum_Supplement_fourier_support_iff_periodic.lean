-- Prove2me | Theorems.Thm_FourierDimTesting102_Quantum_Supplement_fourier_support_iff_periodic
-- name    : FourierDimTesting102.Quantum.Supplement.fourier_support_iff_periodic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T03:27:20.809548+00:00
-- url     : https://prove2.me/theorems/9ebe5d46-f980-49df-a35e-a220b04f80af
-- title:
--   Lemma 3.4 — Fourier support in $U$ iff invariance under every translation in $U^\perp$
-- statement:
--   Let $U\le\mathbb F_2^n$ be a linear subspace, $U^\perp=\{h:\langle u,h\rangle=0\text{ for all }u\in U\}$ its annihilator, and $f$ a boolean function on $\mathbb F_2^n$. Write $C_U$ for the boolean functions whose Fourier support $\{s:\widehat f(s)\neq0\}$ lies in $U$. Then
--
--   $$
--   f\in C_U\iff f(x+h)=f(x)\ \text{ for all }h\in U^\perp\text{ and all }x\in\mathbb F_2^n .
--   $$
--
--   Thus a function has its spectrum in $U$ exactly when it is constant on every coset of $U^\perp$. This links Fourier dimension to periodicity, which the lower bound (Theorem 3.2) and the classical tester (Theorem 4.1) use.
--
--   Differences from the source:
--   - encoding: boolean functions f : F₂ⁿ → {−1,1} → f is its bit function BoolFn n := (Fin n → ZMod 2) → Bool, with sign toSign f x = (−1)^{f x} (the base Model); reason: a bijection on the same functions; the bit is what the oracle returns
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.17, Lemma 3.4

import Definitions.Def_FourierDimTesting102_Quantum_Model

namespace FourierDimTesting102.Quantum.Supplement

open QAlgorithms FourierDimTesting102.Quantum

/-- Lemma 3.4, p.17: `f ∈ C_U` (every frequency with `f̂(s) ≠ 0` lies in `U`) if and only if
`f(x + h) = f(x)` for every `h ∈ U^⊥` and every `x ∈ F₂ⁿ`. -/
theorem fourier_support_iff_periodic {n : ℕ} (U : Submodule (ZMod 2) (V n)) (f : BoolFn n) :
    f ∈ CU U ↔ ∀ h ∈ perp U, ∀ x : V n, f (x + h) = f x := by sorry

end FourierDimTesting102.Quantum.Supplement
