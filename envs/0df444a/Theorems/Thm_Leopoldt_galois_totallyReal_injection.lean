-- Prove2me | Theorems.Thm_Leopoldt_galois_totallyReal_injection
-- name    : Leopoldt.galois_totallyReal_injection
-- status  : Open
-- author  : @WillR
-- created : 2026-09-09T22:37:20.076097+00:00
-- url     : https://prove2.me/theorems/72de39a4-8e5e-4773-a667-ef6a0d4f431c
-- title:
--   Continuous unit injection for totally real Galois fields
-- statement:
--   Let p be an odd prime and let L be a totally real number field that is Galois over Q. Prove the core p-adic regulator assertion that there exists a continuous injective group homomorphism from Multiplicative (Fin (Units.rank L) -> Z_[p]) into the semilocal units at p, with every value lying in the p-adic unit closure of the global units. By the established characterization of Leopoldt's conjecture as the existence of exactly this injection, this lemma is the analytic core needed for the Galois totally real case.
-- source:
--   Core p-adic regulator formulation equivalent to Leopoldt's conjecture via Leopoldt.leopoldtConjecture_iff_exists_continuous_injection; the Galois totally real case is the research-scale case isolated in Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, Section 1.1.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem galois_totallyReal_injection (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (L : Type*) [Field L] [NumberField L] [IsTotallyReal L] [IsGalois ℚ L] :
    ∃ f : Multiplicative (Fin (Units.rank L) → ℤ_[p]) →* SemilocalUnits p L,
      Function.Injective f ∧ Continuous f ∧ ∀ x, f x ∈ unitClosure p L := by sorry
end Leopoldt
