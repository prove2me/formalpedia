-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_flip_list_path_semantics
-- name    : KSATSingleFlip.Connect.flip_list_path_semantics
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:24:35.779513+00:00
-- url     : https://prove2.me/theorems/faf2d8b8-ebd7-4e44-bb87-a9cba40efd7e
-- title:
--   Compact flip lists represent satisfying single-variable paths
-- statement:
--   Suppose a compact flip-list path has every expanded assignment satisfying the formula. Its expansion is a satisfying single-variable path from its initial to its terminal assignment, with length equal to the number of listed flips. If the list has no repeated variable, its endpoint differs from its start exactly on the listed variables.
-- source:
--   Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, model printed p. 2 and compact path representation printed p. 32 (PDF p. 34), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SparseFlip

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- Compact flip lists expand to satisfying single-variable paths with exact length. -/
theorem flip_list_path_semantics {n : ℕ} (p : FlipListPath n) (Φ : GFormula (Fin n))
    (hs : p.Satisfies Φ) :
    IsSatPath Φ p.states p.initial p.terminal ∧
    pathLength p.states = p.flips.length ∧
    (p.flips.Nodup → disagree p.initial p.terminal = p.flips.toFinset) := by
  sorry

end KSATSingleFlip.Connect
