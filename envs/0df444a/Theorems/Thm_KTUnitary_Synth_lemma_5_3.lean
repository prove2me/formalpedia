-- Prove2me | Theorems.Thm_KTUnitary_Synth_lemma_5_3
-- name    : KTUnitary.Synth.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:33:14.962885+00:00
-- url     : https://prove2.me/theorems/08eff3a0-77ec-4ff2-ab60-c65c416ba7a4
-- title:
--   Lemma 5.3 — approximate implementations are close to extensions
-- statement:
--   Let $U$ be an $n$-qubit unitary and $C$ an $(n+a)$-qubit unitary matrix such that, for all $n$-qubit states $|\psi\rangle$,
--   $$\big\|C|\psi\rangle|0^a\rangle-(U|\psi\rangle)|0^a\rangle\big\|\le\varepsilon/2 .$$
--   Then there exists an $a$-qubit extension $\bar U$ of $U$ satisfying
--   $$\|C-\bar U\|_{\mathrm{op}}\le\varepsilon .$$
--
--   The lemma shows that the operator-norm requirement of $\mathsf{unitaryP}$ and $\mathsf{unitaryPSPACE}$ can be checked on the zero-ancilla subspace only, at the cost of a factor $2$.
--
--   Differences from the source:
--   - encoding: (n + a)-qubit matrices acting on |ψ⟩|0^a⟩ → matrices over Bits N with n ≤ N, input on the first n wires, ancillas on the last N − n; reason: a qubit-ordering convention; same statement
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Lemma 5.3, p. 16

import Mathlib
import Definitions.Def_KTUnitary_Synth_vecNorm
import Definitions.Def_KTUnitary_Synth_opNorm
import Definitions.Def_KTUnitary_Synth_ancPad
import Definitions.Def_KTUnitary_Synth_IsExtension

open QAlgorithms.Complexity

namespace KTUnitary.Synth

/-- **Lemma 5.3** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Lemma 5.3, p. 16; approximate implementations are close to extensions).
Let `C` be an `(n + a)`-qubit unitary matrix such that, for all `n`-qubit states `|ψ⟩`,
`‖C |ψ⟩|0^a⟩ − (U |ψ⟩) |0^a⟩‖ ≤ ε/2`. Then there exists an `a`-qubit extension `Ū` of `U` satisfying
`‖C − Ū‖_op ≤ ε`.

**Formalization Note** `N = n + a` with `n ≤ N`; `U` is an `n`-qubit unitary (the setting of
Definition 5.1); states are unit vectors; the ancillas are the last `N − n` wires. -/
theorem lemma_5_3 {n N : ℕ} (h : n ≤ N) (U : Matrix (Bits n) (Bits n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Bits n) ℂ) (C : Matrix (Bits N) (Bits N) ℂ)
    (hC : C ∈ Matrix.unitaryGroup (Bits N) ℂ) (ε : ℝ)
    (hε : ∀ ψ : Bits n → ℂ, vecNorm ψ = 1 →
      vecNorm (C.mulVec (ancPad h ψ) - ancPad h (U.mulVec ψ)) ≤ ε / 2) :
    ∃ Ub : Matrix (Bits N) (Bits N) ℂ, IsExtension h U Ub ∧ opNorm (C - Ub) ≤ ε := by sorry

end KTUnitary.Synth
