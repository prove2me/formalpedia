-- Prove2me | Theorems.Thm_LefebvreVariations_ame_five_two
-- name    : LefebvreVariations.ame_five_two
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:46:33.134791+00:00
-- url     : https://prove2.me/theorems/b8915190-e71e-4c17-8088-852c1dabbb2f
-- title:
--   Lefebvre's variations, No. 64 — on a theme by Open Quantum Problem 35: an absolutely maximally entangled state of five qubits exists
-- statement:
--   There is a unit vector $\psi\in(\mathbb{C}^2)^{\otimes 5}$ that is **absolutely maximally entangled**: for every permutation $\pi$ of the five tensor factors, the reduced density matrix of $\pi\psi$ on its first two factors is maximally mixed,
--   $$
--   \operatorname{Tr}_{3,4,5}\,|\pi\psi\rangle\langle\pi\psi| \;=\; \tfrac14\,\mathbb{1}_{4}.
--   $$
--   In other words, $\mathrm{AME}(5,2)$ exists: five qubits can be prepared so that every pair of them is maximally mixed.
--
--   This is the case $n=5$, $d=2$ of the question for which $(n,d)$ an $\mathrm{AME}(n,d)$ state exists, the question behind the mission target $\mathrm{AME}(12,5)$. The state is the one underlying the five-qubit perfect quantum error-correcting code $[[5,1,3]]$.
--
--   **Formalization Note** The statement is `ExistsAME 5 2` in the platform definitions `Def_AME125_Defs`: `ExistsAME n d` asks for a vector `ψ : EuclideanSpace ℂ (Fin n → Fin d)` of norm $1$ such that for every `π : Equiv.Perm (Fin n)` the reduced density matrix on the first `n / 2` factors of `permuteState π ψ` equals `maximallyMixed (n/2) d`, that is $d^{-n/2}$ times the identity. Here `n / 2 = 2` (integer division) and `d = 2`. Only reductions to two factors are required, which for $n=5$ is the full AME condition (a reduction to three factors is the complement of one to two).
--
--   **Why this is a variation.** Variation on the open Open Quantum Problem 35 (existence of absolutely maximally entangled AME(n,d) states, mission target AME(12,5)). It is the case n = 5, d = 2, the smallest qubit case beyond the Bell pair and with a nontrivial answer, stated with the parent's own definitions; an explicit state with a finite check over the 120 permutations is a model for attacking larger (n,d).
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Five-qubit perfect code [[5,1,3]]: C. H. Bennett, D. P. DiVincenzo, J. A. Smolin and W. K. Wootters, Mixed-state entanglement and quantum error correction, Phys. Rev. A 54 (1996) 3824, and R. Laflamme, C. Miquel, J. P. Paz and W. H. Zurek, Perfect quantum error correcting code, Phys. Rev. Lett. 77 (1996) 198 (both cited from memory; volumes and pages not re-checked). That such a code gives an AME(5,2) state is in A. Higuchi and A. Sudbery, How entangled can two couples get?, Phys. Lett. A 273 (2000) 213, and A. J. Scott, Phys. Rev. A 69 (2004) 052330 (cited from memory; exact attributions not verified). Origin of this statement: the case n = 5, d = 2 of Open Quantum Problem 35 of the IQOQI Vienna list (platform family OpenQuantumProblem35, mission target AME(12,5)).

import Mathlib
import Definitions.Def_AME125_Defs

set_option autoImplicit false

namespace LefebvreVariations

open OpenQuantumProblem35

/-- **An absolutely maximally entangled state of five qubits.** `ExistsAME 5 2` holds: there is a unit
vector of `(ℂ²)^{⊗5}` all of whose two-qubit reductions (for every choice of the two qubits kept, in
every order) are maximally mixed. It is the `n = 5`, `d = 2` instance of the problem of which
`AME(n, d)` exist (Open Quantum Problem 35 of the IQOQI Vienna list, whose mission target is the
`n = 12`, `d = 5` case). The state is the five-qubit perfect code `[[5, 1, 3]]` of Bennett–DiVincenzo–
Smolin–Wootters, *Mixed-state entanglement and quantum error correction*, Phys. Rev. A 54 (1996) 3824,
and Laflamme–Miquel–Paz–Zurek, Phys. Rev. Lett. 77 (1996) 198 (both cited from memory); its
identification as an `AME(5, 2)` state is in Higuchi–Sudbery, Phys. Lett. A 273 (2000) 213, and Scott,
Phys. Rev. A 69 (2004) 052330 (cited from memory).

**Formalization Note.** `ExistsAME`, `IsAME` and the other notions are the platform definitions
`Def_AME125_Defs` in namespace `OpenQuantumProblem35`. -/
theorem ame_five_two : ExistsAME 5 2 := by
  sorry

end LefebvreVariations
