-- Prove2me | Theorems.Thm_Nullstellensatz_zariski_lemma
-- name    : Nullstellensatz.zariski_lemma
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T01:36:04.143988+00:00
-- url     : https://prove2.me/theorems/6bf6f39b-be55-4d57-a1c1-d4349821f89a
-- title:
--   Zariski's lemma
-- statement:
--   Let $K$ be a field and $L$ a field which is finitely generated as an algebra over $K$. Then $L$ is a finite extension of $K$:
--   $$\dim_K L < \infty.$$
--
--   Zariski's lemma is the algebraic input for the proof of the weak Nullstellensatz via maximal ideals.
-- source:
--   Wikipedia, article "Hilbert's Nullstellensatz" (snapshot supplied as Hilbert's_Nullstellensatz.pdf, printed 2026-09-27), https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz, section "Proofs", subsection "Using Zariski's lemma", first sentence.

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem zariski_lemma {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.FiniteType K L] :
    Module.Finite K L := by sorry

end Nullstellensatz
