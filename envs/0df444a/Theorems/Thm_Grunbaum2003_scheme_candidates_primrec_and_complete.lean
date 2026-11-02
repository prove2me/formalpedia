-- Prove2me | Theorems.Thm_Grunbaum2003_scheme_candidates_primrec_and_complete
-- name    : Grunbaum2003.scheme_candidates_primrec_and_complete
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T18:01:10.094776+00:00
-- url     : https://prove2.me/theorems/c82fcee0-3c7b-4fa2-97f3-3a9ae6a0f236
-- title:
--   Scheme candidates primrec and complete
-- statement:
--   For a vertex-label bound $k$, let $R_k$ be the list of all sublists of $[0,\ldots,k-1]$, and let $C_k$ be the list of all sublists of $R_k$.
--
--   The function $k\mapsto C_k$ is primitive recursive. Moreover, whenever a scheme $S$ on $k$ labels realizes a full-dimensional polytope in $\mathbb R^d$, there is a candidate $T\in C_k$ such that every polytope realizing $S$ also realizes $T$.
--
--   This provides a finite effective search space containing representatives of all realized schemes. It does not decide which candidates are realizable and does not remove combinatorial duplicates.
-- source:
--   Elementary finite-search consequence of the published Grunbaum2003.SchemeRealizes definition, supporting Grünbaum (2003), §5.5, effective enumeration. https://prove2.me/theorems/5572322a-bb1c-4c10-afb4-a57ade4996f5

import Definitions.Def_Grunbaum2003_SchemeRealizes
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Range
import Mathlib.Data.Finset.Basic
import Mathlib.Computability.Partrec

set_option autoImplicit false

namespace Grunbaum2003

theorem scheme_candidates_primrec_and_complete :
    Primrec (fun k : ℕ => ((List.range k).sublists').sublists') ∧
    ∀ {d k : ℕ} {S : List (List ℕ)} {P : Set (Fin d → ℝ)},
      SchemeRealizes k S P →
      ∃ T ∈ ((List.range k).sublists').sublists',
        ∀ Q : Set (Fin d → ℝ), SchemeRealizes k S Q → SchemeRealizes k T Q := by sorry

end Grunbaum2003
