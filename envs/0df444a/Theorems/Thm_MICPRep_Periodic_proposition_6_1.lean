-- Prove2me | Theorems.Thm_MICPRep_Periodic_proposition_6_1
-- name    : MICPRep.Periodic.proposition_6_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:34.338468+00:00
-- url     : https://prove2.me/theorems/8e3ba733-c5a4-4770-bee9-8d50c5153510
-- title:
--   Proposition 6.1, p. 22 — S ⊆ S₀ ∪ ⋃ Tᵢ ⊆ cl(S) with S₀ binary MICP-R and each Tᵢ having a nearly periodic MICP formulation
-- statement:
--   Let $M \subseteq \mathbb R^{n+p+d}$ be closed and convex such that $(M, d)$ induces a rational MICP formulation of $S \subseteq \mathbb R^n$. If $D_{\mathrm{MICP}}(M) < \infty$, then there are a binary MICP-R set $S_0$, $k \in \mathbb Z_+$ and sets $T_1, \dots, T_k$, each with a nearly periodic MICP formulation, such that
--   $$S \subseteq S_0 \cup \bigcup_{i=1}^k T_i \subseteq \mathrm{cl}(S).$$
--
--   This is the last step before Theorem 5.1: for closed $S$ the sandwich becomes an equality, and the nearly periodic pieces become closed periodic sets.
--
--   **Formalization Note** $S$ may be empty here. $D_{\mathrm{MICP}}$ is valued in $[0, \infty]$.
-- source:
--   Lubin, Vielma, Zadik, Mixed-integer convex representability, arXiv:1706.05135v3, p. 22, Proposition 6.1

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

namespace MICPRep.Periodic

open scoped ENNReal Matrix

/-- Proposition 6.1, p. 22. -/
theorem proposition_6_1 {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (hD : micpDiam M < ⊤) :
    ∃ S₀ : Set (Pt n), IsBinaryMICPR S₀ ∧
      ∃ (k : ℕ) (T : Fin k → Set (Pt n)),
        (∀ i, HasNearlyPeriodicFormulation (T i)) ∧
        S ⊆ S₀ ∪ ⋃ i, T i ∧ S₀ ∪ ⋃ i, T i ⊆ closure S := by sorry

end MICPRep.Periodic
