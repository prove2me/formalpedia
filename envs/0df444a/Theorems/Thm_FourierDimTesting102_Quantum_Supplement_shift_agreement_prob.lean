-- Prove2me | Theorems.Thm_FourierDimTesting102_Quantum_Supplement_shift_agreement_prob
-- name    : FourierDimTesting102.Quantum.Supplement.shift_agreement_prob
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:28:43.408738+00:00
-- url     : https://prove2.me/theorems/27475dd5-0f1f-42e2-9a7c-5bae4bd9cfd3
-- title:
--   Lemma 4.4 — agreement after a common uniform shift equals the Fourier mass orthogonal to $x+y$
-- statement:
--   Let $f$ be a boolean function on $\mathbb F_2^n$, fix $x,y\in\mathbb F_2^n$ and put $h=x+y$. For $z$ uniform on $\mathbb F_2^n$,
--
--   $$
--   \Pr_z\bigl[f(x+z)=f(y+z)\bigr]=\sum_{S:\langle S,h\rangle=0}\widehat f(S)^2 .
--   $$
--
--   The identity holds for every pair, including $x=y$ (where both sides equal $1$ by Parseval). It turns the collision probability of the tuples of Algorithm 2 into a statement about Fourier samples, and its averaged form underlies Lemma 6.3.
--
--   Differences from the source:
--   - encoding: boolean functions f : F₂ⁿ → {−1,1} → f is its bit function BoolFn n := (Fin n → ZMod 2) → Bool, with sign toSign f x = (−1)^{f x} (the base Model); reason: a bijection on the same functions; the bit is what the oracle returns
--   - encoding: Pr_z for z uniform on F₂ⁿ → unifProb over V n: the number of z with f(x+z) = f(y+z), divided by 2ⁿ; reason: the uniform law on a finite set
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.21, Lemma 4.4

import Definitions.Def_FourierDimTesting102_Quantum_Supplement_Model

namespace FourierDimTesting102.Quantum.Supplement

open QAlgorithms FourierDimTesting102.Quantum

open Classical in
/-- Lemma 4.4, p.21: for fixed `x, y ∈ F₂ⁿ` and `h = x + y`, with `z` uniform on `F₂ⁿ`,
`Pr_z[f(x + z) = f(y + z)] = ∑_{S : ⟨S, h⟩ = 0} f̂(S)²`. -/
theorem shift_agreement_prob {n : ℕ} (f : BoolFn n) (x y : V n) :
    unifProb (fun z : V n => f (x + z) = f (y + z)) =
      ∑ s ∈ Finset.univ.filter (fun s : V n => s ⬝ᵥ (x + y) = 0), coeff f s ^ 2 := by sorry

end FourierDimTesting102.Quantum.Supplement
