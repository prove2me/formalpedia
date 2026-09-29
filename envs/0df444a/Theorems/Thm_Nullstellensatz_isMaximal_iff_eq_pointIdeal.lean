-- Prove2me | Theorems.Thm_Nullstellensatz_isMaximal_iff_eq_pointIdeal
-- name    : Nullstellensatz.isMaximal_iff_eq_pointIdeal
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T01:33:34.276958+00:00
-- url     : https://prove2.me/theorems/938a165d-f397-4e87-b4af-f7979a49e646
-- title:
--   Maximal ideals of $K[X_1,\dots,X_n]$
-- statement:
--   Let $K$ be algebraically closed. An ideal $\mathfrak m$ of $K[X_1,\dots,X_n]$ is maximal if and only if
--   $$\mathfrak m = (X_1 - a_1, \dots, X_n - a_n) \quad \text{for some } a = (a_1,\dots,a_n) \in K^n.$$
--
--   This characterisation of maximal ideals is another common formulation of the weak Nullstellensatz.
-- source:
--   Wikipedia, article "Hilbert's Nullstellensatz" (snapshot supplied as Hilbert's_Nullstellensatz.pdf, printed 2026-09-27), https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz, section "Formulations", paragraph 6 (every maximal ideal is of the form (X_1 - a_1, ..., X_n - a_n)); also section "Proofs / Using Zariski's lemma".

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem isMaximal_iff_eq_pointIdeal {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (m : Ideal (MvPolynomial (Fin n) K)) :
    m.IsMaximal ↔ ∃ a : Fin n → K, m = pointIdeal a := by sorry

end Nullstellensatz
