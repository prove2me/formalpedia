-- Prove2me | Theorems.Thm_MixedCloning_Optimal_werner_pure_fidelity
-- name    : MixedCloning.Optimal.werner_pure_fidelity
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T02:08:26.217604+00:00
-- url     : https://prove2.me/theorems/c9b74423-6aa7-4308-9288-3ef84967b48a
-- title:
--   Bridge to Lemma 7 — Werner's completed cloner on pure tensor powers
-- statement:
--   Let $a$ be a finite set with $D=|a|$ elements, let $n,k\ge0$, and let $\tau$ be any matrix on $(\mathbb C^a)^{\otimes(n+k)}$. Write $D[j]=\binom{j+D-1}{j}$ for the dimension of the symmetric subspace of $(\mathbb C^a)^{\otimes j}$, and $\mathcal C_W$ for Werner's cloner from $n$ to $n+k$ copies, completed by $\tau$ off the symmetric input corner. Let $F(X,Y)=\big(\operatorname{tr}\sqrt{\sqrt X\,Y\sqrt X}\big)^2$ be the squared fidelity. For every unit vector $|v\rangle\in\mathbb C^a$:
--
--   1. $\mathcal C_W\big(|v\rangle\langle v|^{\otimes n}\big)$ is a quantum state;
--   2. its fidelity with the ideal output is
--
--   $$
--   F\Big(\mathcal C_W\big(|v\rangle\langle v|^{\otimes n}\big),\ |v\rangle\langle v|^{\otimes(n+k)}\Big)=\frac{D[n]}{D[n+k]} .
--   $$
--
--   This restates Lemma 7 of the source (Werner's cloner [Wer98]) for the completed map `werner` on which this mission's PCT map is built. The Lemma 7 milestone is linked to a theorem in a different encoding, which also requires $1\le n<n+k$; this bridge covers every $n,k\ge0$ and is stated directly for the mission's map. In the proof of Proposition 10 it is applied with $a$ the index set of $\mathbb C^d\otimes\mathbb C^r$, so $D=dr$, and combined with Lemma 6.
--
--   **Formalization Note** Werner's map is the platform function `werner a n k τ`, and the squared fidelity is `fidelity`, the square of the published root fidelity. The completion term $\operatorname{tr}((I-\Pi_n)X)\,\tau$ vanishes on $|v\rangle\langle v|^{\otimes n}$, so no hypothesis on $\tau$ is needed. The platform's proved theorem `QAlgorithms.Papers.Independent.Support21.P16.canonical_fidelity` gives the same overlap value in a different encoding.
--
--   Differences from the source:
--   - encoding: Werner's map on the symmetric subspace → the map completed by an arbitrary $\tau$; reason: the completion term vanishes on pure tensor powers
--   - addition: the output is a quantum state; reason: implicit in the source, where $\mathcal C_W$ is a channel, and needed to apply data processing of fidelity
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/243.pdf, p. 11, Lemma 7 (Werner's cloner is optimal), citing R. F. Werner, Optimal cloning of pure states, Phys. Rev. A 58, 1827 (1998), https://doi.org/10.1103/PhysRevA.58.1827.

import Definitions.Def_MixedCloning_Optimal_Model

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 7 (PDF p.11), Werner [Wer98], in this mission's encoding: on `|v⟩⟨v|^{⊗n}` the completed
Werner map outputs a state whose fidelity with `|v⟩⟨v|^{⊗(n+k)}` is `D[n]/D[n+k]`, `D = card a`. -/
theorem werner_pure_fidelity {a : Type} [Fintype a] [DecidableEq a] (n k : ℕ) (tau : Op (Word a (n+k)))
    (v : EuclideanSpace ℂ a) (hv : ‖v‖ = 1) :
    IsState (werner a n k tau (tensorPower n (pure v))) ∧
    fidelity (werner a n k tau (tensorPower n (pure v))) (tensorPower (n+k) (pure v)) =
      (symDimension (Fintype.card a) n : ℝ) / symDimension (Fintype.card a) (n+k) := by sorry

end MixedCloning.Optimal
