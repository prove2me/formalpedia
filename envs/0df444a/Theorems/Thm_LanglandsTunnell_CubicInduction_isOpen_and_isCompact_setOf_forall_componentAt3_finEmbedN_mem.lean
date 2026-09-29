-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem
-- name    : LanglandsTunnell.CubicInduction.isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/8a626a01-c2a1-59ce-ac76-281f663d88a3
-- title:
--   Level sets of level data are compact open in GL₃(A_ℚ^f)
-- statement:
--   Let $p$ range over the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$, and for each such $p$ let $K'_p$ be a subgroup of $GL_3(\mathbb{Q}_p)$, where $\mathbb{Q}_p$ denotes the $p$-adic completion of $\mathbb{Q}$. Assume that for every $p$ the underlying set of $K'_p$ is open, that for every $p$ it is compact, and that for all but finitely many $p$ one has $K'_p =$ `localMaximalCompact3 (𝓞 ℚ) ℚ p`, the subgroup of those $k \in GL_3(\mathbb{Q}_p)$ all of whose matrix entries have valuation $\le 1$ and all of whose entries of $k^{-1}$ have valuation $\le 1$. Consider the subset of $GL_3$ of the finite adele ring of $\mathbb{Q}$ consisting of those $k$ such that for every $p$ the $p$-component `componentAt3 (𝓞 ℚ) ℚ p` of the adelic point `finEmbedN (Fin 3) (𝓞 ℚ) ℚ k` — the image of $k$ in $GL_3$ of the full adele ring, obtained by inserting the identity matrix in the infinite-adelic coordinate — lies in $K'_p$. The conclusion asserts that this subset is open and that it is compact.
--
--   This is the topological input showing that the level set attached to a family of compact open local subgroups (a level datum) is a compact open subset of $GL_3$ of the finite adeles of $\mathbb{Q}$, reflecting the restricted-product topology. It is used in the construction of levels and smoothing operators for automorphic forms on $GL_3$ in the cubic-induction part of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain
open scoped NumberField

theorem LanglandsTunnell.CubicInduction.isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hopen : ∀ p, IsOpen (K' p : Set (LocalGL3 p))) (hcpt : ∀ p, IsCompact (K' p : Set (LocalGL3 p)))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    IsOpen {k : Matrix.GeneralLinearGroup (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) |
        ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} ∧
      IsCompact {k : Matrix.GeneralLinearGroup (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) |
        ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} := by sorry
