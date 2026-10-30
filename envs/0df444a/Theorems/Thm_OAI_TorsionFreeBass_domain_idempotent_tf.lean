-- Prove2me | Theorems.Thm_OAI_TorsionFreeBass_domain_idempotent_tf
-- name    : OAI.TorsionFreeBass.domain_idempotent_tf
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:00:39.558022+00:00
-- url     : https://prove2.me/theorems/0d7a744f-7d6a-4f94-8a4c-dcda9bdd061a
-- title:
--   Kaplansky's idempotent conjecture in characteristic zero, for torsion-free groups (OpenAI)
-- statement:
--   For a torsion-free group $G$ (the identity is its only element of finite order) and a commutative integral domain $R$ of characteristic zero, every idempotent $e$ of the group ring $R[G]$ (so $e \cdot e = e$) equals $0$ or $1$. This is the characteristic-zero case of Kaplansky's idempotent conjecture, for coefficient domains and not only fields. Part (ii) of the paper's corollary for torsion-free groups states: "For every commutative unital domain $R$ of characteristic zero, every $e\in RG$ satisfying $e^2=e$ is either $0$ or $1$." The conjecture over fields of positive characteristic is not covered.
--
--   The statement and its proof are OpenAI's (OpenAI, *The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture*, OpenAI Math Release, September 24, 2026, result family 207, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TorsionFreeBass.domain_idempotent` of [lean/OAI/RingTheory/BassTrace/TorsionFree.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/BassTrace/TorsionFree.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a and published here as a named result of the split of OpenAI's proof of `OAI.TorsionFreeBass.torsion_free_corollary`.
--
--   **The statement**, as published (namespace `OAI.TorsionFreeBass`, with `open scoped Classical BigOperators` and `variable {G : Type*} [Group G]`):
--
--   ```lean
--   theorem domain_idempotent_tf (hG : TorsionFree G)
--       (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
--       (e : MonoidAlgebra R G) (he : e * e = e) : e = 0 ∨ e = 1
--   ```
--
--   **Definitions.** `OAI.TorsionFreeBass.TorsionFree` comes from the published bundle `Def_BassTorsionFree`; the group ring is Mathlib's `MonoidAlgebra R G`.
--
--   **Used by.** The proof of `OAI.TorsionFreeBass.torsion_free_corollary` of this split imports it.
-- source:
--   OpenAI, The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 207; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026.pdf, corollary for torsion-free groups, part (ii); Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/BassTrace/TorsionFree.lean (declaration OAI.TorsionFreeBass.domain_idempotent)

import Mathlib
import Definitions.Def_BassTorsionFree

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Classical BigOperators
noncomputable section
namespace TorsionFreeBass

variable {G : Type*} [Group G]

theorem domain_idempotent_tf (hG : TorsionFree G)
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (e : MonoidAlgebra R G) (he : e * e = e) : e = 0 ∨ e = 1 := by
  sorry

end TorsionFreeBass
end

end OAI
end
