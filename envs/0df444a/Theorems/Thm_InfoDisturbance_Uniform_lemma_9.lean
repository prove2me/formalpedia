-- Prove2me | Theorems.Thm_InfoDisturbance_Uniform_lemma_9
-- name    : InfoDisturbance.Uniform.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:38.985221+00:00
-- url     : https://prove2.me/theorems/9a899e49-ae5e-48ca-89e6-e6000a2968b0
-- title:
--   Lemma 9, p. 12 — second moment Π of the uniform pure-state ensemble
-- statement:
--   Let $\Omega$ be the unitarily invariant probability measure on unit vectors of $\mathbb C^d$, $d\ge1$, and let
--   $$\Pi:=\int d\Omega_\psi\,|\psi\rangle\langle\psi|\otimes|\psi\rangle\langle\psi| .$$
--   Then
--   $$\Pi=\frac{1}{d(d+1)}\sum_{i,j}\Big(|i\rangle\langle i|\otimes|j\rangle\langle j|+|i\rangle\langle j|\otimes|j\rangle\langle i|\Big),$$
--   that is, $\Pi=(I+\mathrm{SWAP})/(d(d+1))$, where $\{|i\rangle\}$ is the standard basis.
--
--   Every average of a product of two quadratic forms over $\Omega$ follows from this identity; it is the computational core of Theorem 8.
--
--   **Formalization Note** $\Pi$ is `secondMoment d hd`, defined entrywise. $|i\rangle\langle j|$ is `Matrix.single i j 1`, and $\otimes$ is the Kronecker product `⊗ₖ` on `Fin d × Fin d`.
-- source:
--   Barnum, Information-disturbance tradeoff in quantum measurement on the uniform ensemble, arXiv:quant-ph/0205155v1, p. 12, Lemma 9, Eqs. (26)–(27)

import Mathlib
import Definitions.Def_InfoDisturbance_Uniform_Model
open scoped Matrix ComplexOrder Kronecker
open QAlgorithms QAlgorithms.QuditFidelity MeasureTheory

namespace InfoDisturbance.Uniform

theorem lemma_9 (d : ℕ) (hd : 0 < d) :
    secondMoment d hd
      = (1 / ((d : ℂ) * ((d : ℂ) + 1))) •
          ∑ i : Fin d, ∑ j : Fin d,
            (Matrix.single i i (1 : ℂ) ⊗ₖ Matrix.single j j (1 : ℂ)
              + Matrix.single i j (1 : ℂ) ⊗ₖ Matrix.single j i (1 : ℂ)) := by sorry

end InfoDisturbance.Uniform
