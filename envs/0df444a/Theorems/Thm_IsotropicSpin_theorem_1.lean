-- Prove2me | Theorems.Thm_IsotropicSpin_theorem_1
-- name    : IsotropicSpin.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:26:30.738203+00:00
-- url     : https://prove2.me/theorems/9c7c7741-f0f8-419d-bdcd-eb5b2b082455
-- title:
--   Theorem 1 — $S[\Lambda_{1/2}]=\log3-\tfrac23\log2$ and $S[\Lambda_1]=\log2$
-- statement:
--   Let $\Lambda_{1/2}$ and $\Lambda_1$ be the isotropic spin channels
--
--   $$
--   \Lambda_s(\rho)=\frac1{s(s+1)}\sum_{k=1}^3S_k\rho S_k
--   $$
--
--   of eq. (6), for spin $1/2$ ($S_k=\tfrac12\sigma_k$, the Pauli matrices) and for spin $1$ (the matrices (13)). For a channel $\Lambda$ let $S[\Lambda]$ be its minimal entropy output (1), the infimum of the von Neumann entropy $S(\Lambda(\rho))$ over density matrices $\rho$, which equals the infimum of $S(\Lambda(|\phi\rangle\langle\phi|))$ over unit vectors $\phi$. Then
--
--   $$
--   S[\Lambda_{1/2}]=\log 3-\frac23\log 2\qquad(9),\qquad\qquad S[\Lambda_1]=\log 2\qquad(10).
--   $$
--
--   Each value is stated for both forms of the infimum (1), and each of the four sets of output entropies is bounded below.
--
--   The paper uses these values in Theorem 2 to show that a maximally entangled input to $\Lambda_s\otimes\Lambda_s$ gives strictly more than $2S[\Lambda_s]$, which is consistent with additivity of the minimal entropy output.
--
--   **Formalization Note** The two infima are `minEntropyOutput` (over density matrices) and the published `WHAdditivity.Renyi.minOutputEntropy 1` (over unit vectors); both are real `sInf`.
--
--   Differences from the source:
--   - encoding: log (no base stated) → Real.log, the natural logarithm, inside the von Neumann entropy WHAdditivity.Renyi.vonNeumannEntropy (0 log 0 = 0); reason: Lean convention; every term of the statement scales by the same factor under a change of base
--   - encoding: S[Λ] = inf (an extended-real infimum) → real sInf, together with BddBelow of the set of values; reason: real sInf is 0 on a set unbounded below; concluding BddBelow makes the equalities the page's
--   - encoding: Λ_s defined on density matrices by (6) with "the notation of above" → isotropicChannel s S on all square matrices, S = spinHalf (½σ_k) or spinOne ((13)), bases (|+1/2⟩, |−1/2⟩) and (|+1⟩, |0⟩, |−1⟩); reason: linear extension of the same formula; on density matrices the values are the page's
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, Theorem 1, eqs. (9)–(10), p.2

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_IsotropicSpin_spinHalf
import Definitions.Def_IsotropicSpin_spinOne
import Definitions.Def_IsotropicSpin_isotropicChannel
import Definitions.Def_IsotropicSpin_densityOutputEntropies
import Definitions.Def_IsotropicSpin_minEntropyOutput

namespace IsotropicSpin

/-- **Theorem 1**, Alicki, *Isotropic quantum spin channels and additivity questions*,
arXiv:quant-ph/0402080v1, p. 2, eqs. (9)–(10): the minimal entropy outputs of the isotropic spin
channels (6) are `S[Λ_{1/2}] = log 3 − (2/3) log 2` and `S[Λ₁] = log 2`.

Each value is stated for both forms of the minimal entropy output (1): the infimum of `S(Λ(ρ))`
over density matrices `ρ` (`minEntropyOutput`) and the infimum of `S(Λ(|φ⟩⟨φ|))` over unit vectors
`φ` (`WHAdditivity.Renyi.minOutputEntropy 1`), together with the boundedness below of each set of
values.

**Formalization Note** Natural logarithm throughout (the paper's `log` has no stated base; both
sides of (9) and (10) scale alike). The infima are real `sInf`, so `BddBelow` is concluded. The
channels are `Λ_{1/2} = isotropicChannel (1/2) spinHalf` (`S_k = σ_k/2`) and
`Λ₁ = isotropicChannel 1 spinOne` (the matrices (13)). -/
theorem theorem_1 :
    (BddBelow (densityOutputEntropies (isotropicChannel (1 / 2) spinHalf)) ∧
      minEntropyOutput (isotropicChannel (1 / 2) spinHalf) = Real.log 3 - 2 / 3 * Real.log 2 ∧
      BddBelow (WHAdditivity.Renyi.outputEntropies 1 (isotropicChannel (1 / 2) spinHalf)) ∧
      WHAdditivity.Renyi.minOutputEntropy 1 (isotropicChannel (1 / 2) spinHalf) =
        Real.log 3 - 2 / 3 * Real.log 2) ∧
    (BddBelow (densityOutputEntropies (isotropicChannel 1 spinOne)) ∧
      minEntropyOutput (isotropicChannel 1 spinOne) = Real.log 2 ∧
      BddBelow (WHAdditivity.Renyi.outputEntropies 1 (isotropicChannel 1 spinOne)) ∧
      WHAdditivity.Renyi.minOutputEntropy 1 (isotropicChannel 1 spinOne) = Real.log 2) := by sorry

end IsotropicSpin
