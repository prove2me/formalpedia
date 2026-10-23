-- Prove2me | Theorems.Thm_MICPRep_Periodic_lemma_6_1
-- name    : MICPRep.Periodic.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:20.827011+00:00
-- url     : https://prove2.me/theorems/94c7412c-1ebe-4439-93b0-e44d695f9995
-- title:
--   Lemma 6.1, p. 21 — a rational MICP-R set splits into a binary MICP-R set and rational pieces whose I_ℤ has an integer point in its relative interior
-- statement:
--   Let $M \subseteq \mathbb R^{n+p+d}$ be closed and convex such that $(M, d)$ induces a rational MICP formulation of a nonempty set $S \subseteq \mathbb R^n$. Then there are a binary MICP-R set $S_0 \subseteq \mathbb R^n$, $k \in \mathbb Z_+$ and closed convex sets $M_1, \dots, M_k \subseteq \mathbb R^{n+p+d}$ such that each $(M_i, d)$ induces a rational MICP formulation of a nonempty set $S_i$,
--   $$S = S_0 \cup \bigcup_{i=1}^k S_i,$$
--   and for each $i$, with $I_i$ the index set of $(M_i, d)$,
--   $$D_{\mathrm{MICP}}(M_i) \le D_{\mathrm{MICP}}(M) \quad (6.2a), \qquad (I_i)_{\mathbb Z} \text{ has an integer point in its relative interior} \quad (6.2b).$$
--
--   This is the first of the two key lemmas behind Theorem 5.1: it reduces to formulations whose index sets are "integrally full-dimensional".
--
--   **Formalization Note** The sets $M_i$ live in the same $\mathbb R^{n+p+d}$ as $M$ (same $p$ and $d$), as "$(M_i, d)$" says; the relative interior is `intrinsicInterior`.
-- source:
--   Lubin, Vielma, Zadik, Mixed-integer convex representability, arXiv:1706.05135v3, p. 21, Lemma 6.1

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

namespace MICPRep.Periodic

open scoped ENNReal Matrix

/-- Lemma 6.1, p. 21. -/
theorem lemma_6_1 {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (hS : S.Nonempty) :
    ∃ S₀ : Set (Pt n), IsBinaryMICPR S₀ ∧
      ∃ (k : ℕ) (Ms : Fin k → Set (Ambient n p d)) (Ss : Fin k → Set (Pt n)),
        (∀ i, IsRationalFormulation (Ms i) (Ss i) ∧ (Ss i).Nonempty) ∧
        S = S₀ ∪ ⋃ i, Ss i ∧
        ∀ i, micpDiam (Ms i) ≤ micpDiam M ∧
          (intrinsicInterior ℝ (IZ (indexSet (Ms i))) ∩ intLattice d).Nonempty := by sorry

end MICPRep.Periodic
