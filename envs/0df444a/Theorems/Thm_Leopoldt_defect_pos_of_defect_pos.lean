-- Prove2me | Theorems.Thm_Leopoldt_defect_pos_of_defect_pos
-- name    : Leopoldt.defect_pos_of_defect_pos
-- status  : Proved
-- author  : @kbuzzard
-- created : 2026-09-09T09:33:39.805255+00:00
-- url     : https://prove2.me/theorems/e48e8919-94ab-4253-b607-4ea2b598d426
-- title:
--   A positive Leopoldt defect is inherited by finite extensions
-- statement:
--   This is part A of Remark 1 of the source.
--
--   Let $p$ be a prime and let $\mathbb{F} \subseteq \mathbb{K}$ be number fields with $\mathbb{K}/\mathbb{F}$ a finite extension. If the Leopoldt defect of $\mathbb{F}$ at $p$ is positive, then so is that of $\mathbb{K}$:
--   $$\mathcal{D}_L(\mathbb{F}) > 0 \quad \Longrightarrow \quad \mathcal{D}_L(\mathbb{K}) > 0 .$$
--
--   The reason given in the source is that the linear relations between $\mathbb{Z}$-generators of the units of $\mathbb{F}$ which arise upon $p$-adic completion are preserved under the embedding of unit groups $E(\mathbb{F}) \hookrightarrow E(\mathbb{K})$.
--
--   This is the structural fact that makes a proof by contradiction possible at all: if the conjecture fails for some field, one may pass freely to any convenient finite extension — larger, containing prescribed roots of unity, or with prescribed ramification — and the failure persists. The source uses exactly this to move from a hypothetical counterexample to a well-adapted working base field. Contrapositively, Leopoldt's conjecture for a field implies it for every subfield.
--
--   **Formalization Note** Finiteness of $\mathbb{K}/\mathbb{F}$ is expressed as $\mathbb{K}$ being a finite-dimensional $\mathbb{F}$-vector space; both fields carry the assumption of being number fields, and $\mathbb{K}$ is an $\mathbb{F}$-algebra, which is how the inclusion $\mathbb{F} \subseteq \mathbb{K}$ is presented. Positivity of a natural-number defect is the same as its non-vanishing.
-- source:
--   Preda Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544, Section 1.3 (Plan of the proof), Remark 1 part A (LaTeX label 'shift'), p. 5: 'If K_start is a field for which D_L(K_start) > 0, then it is known that the same holds for arbitrary finite algebraic extensions K/K_start; this is noted, for instance, by Laurent in the introduction to [Lau].' Cited original: M. Laurent, Rang p-adique d'unites et action de groupes, J. reine angew. Math. 399 (1989), 81-108.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem defect_pos_of_defect_pos (p : ℕ) [Fact p.Prime]
    (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [FiniteDimensional F K] (h : 0 < defect p F) :
    0 < defect p K := by sorry
end Leopoldt
