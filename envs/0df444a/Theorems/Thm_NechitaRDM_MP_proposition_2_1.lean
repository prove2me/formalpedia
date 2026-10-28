-- Prove2me | Theorems.Thm_NechitaRDM_MP_proposition_2_1
-- name    : NechitaRDM.MP.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:43.026657+00:00
-- url     : https://prove2.me/theorems/300aa08e-6212-4cd3-8dfa-4a383aee9722
-- title:
--   Proposition 2, item 1, p. 4 — the class of a complex Gaussian vector X ∼ N^n_ℂ(0, Iₙ) is distributed along νₙ
-- statement:
--   Let $n \ge 1$ and let $X$ be a random vector of $\mathbb C^n$ with law $\mathcal N^n_{\mathbb C}(0, I_n)$, i.e. with independent coordinates of law $\mathcal N_{\mathbb C}(0,1)$. Then the class $|X\rangle$ of $X$, i.e. the pure density matrix
--   $$|X\rangle\langle X| = \frac{X X^*}{\|X\|^2},$$
--   is distributed along the unique unitarily invariant law $\nu_n$ on pure states: its law is a probability measure carried by the pure density matrices and invariant under every unitary conjugation.
--
--   This gives a concrete way to sample a uniform random pure state, and is the step from the abstract measure $\nu_{nk}$ to Gaussian matrices in Lemma 1.
--
--   **Formalization Note** The conclusion is `IsPureStateLaw` of the image law; by Proposition 1 this is the same as "the law equals $\nu_n$". The event $X = 0$, where $|X\rangle\langle X|$ is set to $0$, is $P$-null and is not excluded by a hypothesis.
-- source:
--   Nechita, Asymptotics of random density matrices, arXiv:quant-ph/0702154v3, p. 4, Proposition 2 (item 1)

import Mathlib
import Definitions.Def_NechitaRDM_MP_Basic

namespace NechitaRDM.MP

open MeasureTheory

/-- **Proposition 2, item 1** (p. 4). If `X ∼ N^n_ℂ(0, Iₙ)`, the class `|X⟩` (here the pure
density matrix `XX*/‖X‖²`) is distributed along `νₙ`. -/
theorem proposition_2_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (X : Ω → (Fin n → ℂ)) (hX : IsComplexGaussianVector P X) :
    IsPureStateLaw (P.map fun ω => pureState (X ω)) := by sorry

end NechitaRDM.MP
