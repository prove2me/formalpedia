-- Prove2me | Theorems.Thm_NechitaRDM_MP_proposition_1
-- name    : NechitaRDM.MP.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:44.501827+00:00
-- url     : https://prove2.me/theorems/8982dcd5-d98e-4f06-a13a-c63d22c59daa
-- title:
--   Proposition 1, p. 4 — there is a unique unitarily invariant probability measure νₙ on the pure states of ℂⁿ
-- statement:
--   Let $n \ge 1$ and let $E_n$ be the set of pure states (rays) of $\mathbb C^n$, identified with the rank-one orthogonal projections $|\psi\rangle\langle\psi|$. Then there exists one and only one probability measure $\nu_n$ on $E_n$ that is unitarily invariant:
--   $$\nu_n(U A) = \nu_n(A) \qquad \text{for all } U \in U(n) \text{ and all Borel } A \subseteq E_n .$$
--
--   This is the canonical ("uniform") law of a random pure state. Its uniqueness is what makes the induced measure $\mu_{n,k}$ of Definition 3 well defined.
--
--   **Formalization Note** The measure lives on $n\times n$ complex matrices and is carried by the pure density matrices (`IsPureDensity`); invariance is invariance under the conjugations $\rho \mapsto U\rho U^*$. The statement is `∃!` over such measures. The paper's proof (transitivity and properness of the action, via Kallenberg's Theorem 1) is not part of the statement.
-- source:
--   Nechita, Asymptotics of random density matrices, arXiv:quant-ph/0702154v3, p. 4, Proposition 1

import Mathlib
import Definitions.Def_NechitaRDM_MP_Basic

namespace NechitaRDM.MP

open MeasureTheory

/-- **Proposition 1** (p. 4). For `n ≥ 1` there is a unique unitarily invariant probability
measure `νₙ` on the pure states of `ℂⁿ` (represented by rank-one projections). -/
theorem proposition_1 (n : ℕ) (hn : 0 < n) :
    ∃! ν : Measure (Matrix (Fin n) (Fin n) ℂ), IsPureStateLaw ν := by sorry

end NechitaRDM.MP
