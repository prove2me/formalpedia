-- Prove2me | Theorems.Thm_LindbladStructLearn_lemma_2_8
-- name    : LindbladStructLearn.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:52:54.07345+00:00
-- url     : https://prove2.me/theorems/906ab97f-ab9d-440d-ad6b-0d7bf4a1d84e
-- title:
--   Lemma 2.8 — local orthonormality relations
-- statement:
--   Let $P_1, P_2, Q_1, Q_2 \in \mathcal P_n$ and let $S \subseteq [n]$ contain $S_{\overline P} = \mathrm{supp}(P_1)\cup\mathrm{supp}(P_2)$. Then
--
--   $$\mathbb E_{R\sim\mathcal P_S}\Big[\overline{\mathrm{tr}}\big(\chi_{P_1,P_2}(R)^\dagger\cdot\chi_{Q_1,Q_2}(R)\big)\Big] = \begin{cases}1 & \text{if } Q_1^S = P_1,\ Q_2^S = P_2 \text{ and } Q_1^{\overline S} = Q_2^{\overline S},\\ 0 & \text{otherwise,}\end{cases}$$
--
--   where $R$ is uniform over the Paulis supported in $S$, $Q^S$ is $Q$ on $S$ and the identity elsewhere, and $\overline S$ is the complement of $S$.
--
--   With random Paulis restricted to a local set, the Fourier functions are no longer orthonormal: $\chi_{P_1,P_2}$ is confused exactly with the pairs that agree with it on $S$ and are equal off $S$. This is what makes local Fourier coefficients sums of global ones.
--
--   Differences from the source: none.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Lemma 2.8, Eq. (2.17), p.15

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_pauliAvg
import Definitions.Def_LindbladStructLearn_chi
import Definitions.Def_LindbladStructLearn_ntr
import Definitions.Def_LindbladStructLearn_restrict
import Definitions.Def_LindbladStructLearn_pairSupport

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Lemma 2.8 (local orthonormality relations; Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Eq. (2.17), p.15): for
`P₁, P₂, Q₁, Q₂ ∈ 𝒫_n` and `S ⊇ S_P̄`, `E_(R∼𝒫_S) [tr̄(χ_(P₁,P₂)(R)† · χ_(Q₁,Q₂)(R))]` is `1` if
`Q₁^S = P₁`, `Q₂^S = P₂` and `Q₁^(S̄) = Q₂^(S̄)`, and `0` otherwise.

**Formalization Note** `Q^S` is `Q` on `S`, identity off `S` (`restrict`); `S̄` is the complement
(the bar is lost in the text layer, checked on the rendered page). -/
theorem lemma_2_8 {n : ℕ} (P1 P2 Q1 Q2 : Pauli n) (S : Finset (Fin n))
    (hS : pairSupport (P1, P2) ⊆ S) :
    pauliAvg S (fun R => ntr ((chi P1 P2 (pauliMatrix R))ᴴ * chi Q1 Q2 (pauliMatrix R))) =
      if restrict S Q1 = P1 ∧ restrict S Q2 = P2 ∧ restrict Sᶜ Q1 = restrict Sᶜ Q2 then 1 else 0 := by sorry

end LindbladStructLearn
