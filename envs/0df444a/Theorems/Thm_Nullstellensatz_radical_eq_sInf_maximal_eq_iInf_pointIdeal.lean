-- Prove2me | Theorems.Thm_Nullstellensatz_radical_eq_sInf_maximal_eq_iInf_pointIdeal
-- name    : Nullstellensatz.radical_eq_sInf_maximal_eq_iInf_pointIdeal
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T01:35:18.394987+00:00
-- url     : https://prove2.me/theorems/71eba7ff-75eb-41ad-b35c-d957c10e4c25
-- title:
--   $\sqrt J$ as an intersection of maximal ideals
-- statement:
--   Let $K$ be algebraically closed and $J$ an ideal of $K[X_1,\dots,X_n]$. Then
--   $$\sqrt J = \bigcap_{\mathfrak m \supseteq J} \mathfrak m = \bigcap_{(a_1,\dots,a_n) \in \mathrm V(J)} (X_1 - a_1, \dots, X_n - a_n),$$
--   where the first intersection is over the maximal ideals $\mathfrak m$ containing $J$.
--
--   **Formalization Note.** An empty intersection is the whole ring, which is the correct value when $J$ is the whole ring.
-- source:
--   Wikipedia, article "Hilbert's Nullstellensatz" (snapshot supplied as Hilbert's_Nullstellensatz.pdf, printed 2026-09-27), https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz, section "Formulations", last display (sqrt J as intersections over maximal ideals and over points of V(J)).

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem radical_eq_sInf_maximal_eq_iInf_pointIdeal {K : Type*} [Field K] [IsAlgClosed K]
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) K)) :
    J.radical = sInf {m | J ≤ m ∧ m.IsMaximal} ∧
      J.radical = ⨅ a ∈ zeroSet J, pointIdeal a := by sorry

end Nullstellensatz
