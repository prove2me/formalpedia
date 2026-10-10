-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedModularGeneralDetectorResources_nativeBudget_eq
-- name    : OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetectorResources_nativeBudget_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T18:03:33.135921+00:00
-- url     : https://prove2.me/theorems/06d72520-3316-46ef-a007-9df6e63254e1
-- title:
--   The native budget of the general detector resources does not depend on L
-- statement:
--   Let $\alpha$ be a semiring, $K$ a `PreparedModularCanonicalDetectorResourceConstants` (a structure of thirteen natural-number constants $m$, `Cperiod`, `Cgrid`, `Acover`, `Asample`, `Cpref`, `Apert`, `AmassWindow`, `Aproj`, `Aside`, `Cnative`, `Anorm`, `Amarginal`), $\mathrm{dim}$ a natural number and $P,L,L'\in\alpha$. Then the `nativeBudget` field of `preparedModularGeneralDetectorResources K dim P L` equals the `nativeBudget` field of `preparedModularGeneralDetectorResources K dim P L'`. Here `preparedModularGeneralDetectorResources K dim P L` is a `PreparedModularCanonicalDetectorResources α`, a structure of 26 elements of $\alpha$ (`Q`, `v`, `w`, `Dg`, …, `nativeBudget`, `E`, `full`, `required`), each given by an explicit polynomial expression in $P$, $L$, $\mathrm{dim}$ and the constants of $K$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetectorResources_nativeBudget_eq` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedModularGeneralDetectorNativeBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B146` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedModularGeneralDetectorNativeBounds.lean#L131

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B146

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem preparedModularGeneralDetectorResources_nativeBudget_eq
    {α : Type*} [Semiring α] (K : PreparedModularCanonicalDetectorResourceConstants)
    (dim : ℕ) (P L L' : α) :
    (preparedModularGeneralDetectorResources K dim P L).nativeBudget =
      (preparedModularGeneralDetectorResources K dim P L').nativeBudget := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
