-- Prove2me | Theorems.Thm_LindbladStructLearn_lemma_2_7
-- name    : LindbladStructLearn.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:52:43.231261+00:00
-- url     : https://prove2.me/theorems/59f3f95e-ad88-40b5-a583-2a9f9a704b8f
-- title:
--   Lemma 2.7 — the Pauli Fourier basis is orthonormal
-- statement:
--   Let $P_1, P_2, Q_1, Q_2 \in \mathcal P_n$ be $n$-qubit Paulis and $\chi_{P_1,P_2}(\rho) = P_1\rho P_2$. Then
--
--   $$\mathbb E_{R\sim\mathcal P_n}\Big[\overline{\mathrm{tr}}\big(\chi_{P_1,P_2}(R)^\dagger\cdot\chi_{Q_1,Q_2}(R)\big)\Big] = \begin{cases}1 & \text{if } P_1 = Q_1 \text{ and } P_2 = Q_2,\\ 0 & \text{otherwise,}\end{cases}$$
--
--   where $R$ is uniform over all $4^n$ Paulis and $\overline{\mathrm{tr}} = \mathrm{tr}/2^n$.
--
--   This orthonormality gives the Fourier inversion formula $\widehat\Phi(P_1,P_2) = \mathbb E_R[\overline{\mathrm{tr}}(\chi_{P_1,P_2}(R)^\dagger\Phi(R))]$ for superoperators.
--
--   Differences from the source: none.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Lemma 2.7, Eq. (2.12), p.15

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_pauliAvg
import Definitions.Def_LindbladStructLearn_chi
import Definitions.Def_LindbladStructLearn_ntr

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Lemma 2.7 (the Fourier basis is orthonormal; Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Eq. (2.12), p.15): for
`P₁, P₂, Q₁, Q₂ ∈ 𝒫_n`, `E_(R∼𝒫_n) [tr̄(χ_(P₁,P₂)(R)† · χ_(Q₁,Q₂)(R))]` is `1` if `P₁ = Q₁` and
`P₂ = Q₂`, and `0` otherwise.

**Formalization Note** `tr̄ = tr/2ⁿ`; `R ∼ 𝒫_n` is the uniform average over all `4ⁿ` Paulis
(`paulisOn univ`). -/
theorem lemma_2_7 {n : ℕ} (P1 P2 Q1 Q2 : Pauli n) :
    pauliAvg Finset.univ (fun R =>
      ntr ((chi P1 P2 (pauliMatrix R))ᴴ * chi Q1 Q2 (pauliMatrix R))) =
      if P1 = Q1 ∧ P2 = Q2 then 1 else 0 := by sorry

end LindbladStructLearn
