-- Prove2me | Theorems.Thm_NishtAbel2024_scope_sn_stability
-- name    : NishtAbel2024.scope_sn_stability
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T20:57:25.063194+00:00
-- url     : https://prove2.me/theorems/71d05a76-5b01-43ad-9939-b3cc898185cb
-- title:
--   Strong normalization under a scoped signature extension
-- statement:
--   Let $\Sigma$ be a closed finite signature with unique names, let $\Xi$ be a mutually recursive block whose names are unique and disjoint from $\Sigma$ and whose declarations refer only to names in $\Sigma\cup\Xi$, and let $t$ be a term whose function references all belong to $\Sigma$. For the reduction relation of the existing NishtAbel2024 Lean formalization,
--
--   $$\operatorname{SN}_{\Sigma,\Xi}(t)\quad\Longleftrightarrow\quad\operatorname{SN}_{\Sigma,\varnothing}(t).$$
--
--   This auxiliary result isolates normalization stability under a fresh signature extension. It does not establish preservation of type interpretations or the semantic soundness theorem.
-- source:
--   Auxiliary lemma for the current Lean formalization inspired by Kanstantsin Nisht, Type-Based Termination Checking in Agda (master’s thesis, supervised by Andreas Abel), https://knisht.github.io/agda/msc.pdf, Section 5.4.2, pp. 36–37; this exact scoping predicate and iff theorem are not stated verbatim in the thesis.

import Definitions.Def_NishtAbel2024_Semantics
import Definitions.Def_NishtAbel2024_ScopeAux

namespace NishtAbel2024

/-- Auxiliary normalization stability for an old-scoped term. -/
theorem scope_sn_stability {sig : GlobalSig} {block : MutualBlock}
    (hscope : scopeBlockExtension sig block) {t : Term}
    (ht : ∀ f ∈ scopeTermRefs t, f ∈ scopeNames sig) :
    SN sig block t ↔ SN sig [] t := by
  sorry

end NishtAbel2024
