-- Prove2me | Theorems.Thm_LefebvreVariations_ame_four_three
-- name    : LefebvreVariations.ame_four_three
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:42:00.699444+00:00
-- url     : https://prove2.me/theorems/933c0493-6b76-5978-ab5a-5267425599ba
-- title:
--   Lefebvre's variations, No. 51 — on a theme by Open Quantum Problem 35: an absolutely maximally entangled state of four qutrits exists
-- statement:
--   There is a unit vector $\psi\in(\mathbb{C}^3)^{\otimes 4}$ that is **absolutely maximally entangled**: for every permutation $\pi$ of the four tensor factors, the reduced density matrix of $\pi\psi$ on its first two factors is maximally mixed,
--   $$
--   \operatorname{Tr}_{3,4}\,|\pi\psi\rangle\langle\pi\psi| \;=\; \tfrac19\,\mathbb{1}_{9}.
--   $$
--   In other words, $\mathrm{AME}(4,3)$ exists: four qutrits can be arranged so that every pair of them is maximally entangled with the other pair.
--
--   This is the case $n=4$, $d=3$ of the question for which $(n,d)$ an $\mathrm{AME}(n,d)$ state exists, the question behind the mission target $\mathrm{AME}(12,5)$. For qubits $\mathrm{AME}(4,2)$ does not exist (Higuchi–Sudbery), whereas for qutrits it does; the state is the uniform superposition of the nine codewords of the $[4,2,3]$ MDS code over $\mathbb{F}_3$.
--
--   **Formalization Note** The statement is `ExistsAME 4 3` in the platform definitions `Def_AME125_Defs`: `ExistsAME n d` asks for a vector `ψ : EuclideanSpace ℂ (Fin n → Fin d)` of norm $1$ such that for every `π : Equiv.Perm (Fin n)` the reduced density matrix on the first `n / 2` factors of `permuteState π ψ` equals `maximallyMixed (n/2) d`, that is $d^{-n/2}$ times the identity. Here `n / 2 = 2` and `d = 3`.
--
--   **Why this is a variation.** Variation on the open Open Quantum Problem 35 (existence of absolutely maximally entangled AME(n,d) states, mission target AME(12,5)). It is the case n = 4, d = 3, the smallest even-n entry beyond the known qubit cases, stated with the parent's own definitions; an explicit state and a finite check over the 24 permutations model how larger cases can be attacked.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   A. J. Scott, Multipartite entanglement, quantum-error-correcting codes, and entangling power of quantum evolutions, Phys. Rev. A 69 (2004) 052330 (AME states and MDS codes); existence of AME(4,3) and non-existence of AME(4,2): A. Higuchi and A. Sudbery, How entangled can two couples get?, Phys. Lett. A 273 (2000) 213-217. (Both references are cited from memory and their exact pages were not verified.) Origin of this statement: the case n = 4, d = 3 of the question of which AME(n,d) states exist, Open Quantum Problem 35 of the IQOQI Vienna list, with its mission target AME(12,5), whose formalization is the platform theorem family OpenQuantumProblem35 (e.g. ame_3_exists); the state is the equal superposition of the nine words (a, b, a+b, a+2b) of the [4,2,3] MDS code over F_3, and the proof is a finite check over all 24 permutations of the factors.

import Mathlib
import Definitions.Def_AME125_Defs

set_option autoImplicit false

namespace LefebvreVariations

open OpenQuantumProblem35

/-- **An absolutely maximally entangled state of four qutrits.** `ExistsAME 4 3` holds: there is a unit
vector of `(ℂ³)^{⊗4}` all of whose two-qutrit reductions (for every choice of the two qutrits kept, in
every order) are maximally mixed. It is the `n = 4`, `d = 3` instance of the problem of which `AME(n, d)`
exist (Open Quantum Problem 35 of the IQOQI Vienna list, the `n = 12`, `d = 5` case being the mission
target); Higuchi–Sudbery, *How entangled can two couples get?*, Phys. Lett. A 273 (2000) 213, showed
that `AME(4, 2)` does not exist while `AME(4, 3)` does (cited from memory); the state is the equal
superposition of the nine words of the `[4, 2, 3]` MDS code over `𝔽₃` (Scott, Phys. Rev. A 69 (2004)
052330, cited from memory).

**Formalization Note.** `ExistsAME`, `IsAME` and the other notions are the platform definitions
`Def_AME125_Defs` in namespace `OpenQuantumProblem35`. -/
theorem ame_four_three : ExistsAME 4 3 := by
  sorry

end LefebvreVariations
