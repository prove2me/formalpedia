-- Prove2me | Theorems.Thm_MICPRep_Periodic_lemma_6_2
-- name    : MICPRep.Periodic.lemma_6_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:44.622132+00:00
-- url     : https://prove2.me/theorems/28a377a3-2936-4872-8b2f-dfc3151bedd8
-- title:
--   Lemma 6.2, p. 22 — trichotomy: binary MICP-R, or a nearly periodic formulation, or a rational formulation with d − 1 integer variables sandwiched between S and cl(S)
-- statement:
--   Let $M \subseteq \mathbb R^{n+p+d}$ be closed and convex such that $(M, d)$ induces a rational MICP formulation of a nonempty set $S \subseteq \mathbb R^n$ with index set $I$. If $D_{\mathrm{MICP}}(M) < \infty$ and $I_{\mathbb Z}$ has an integer point in its relative interior, then one of the following holds:
--
--   1. $S$ is binary MICP-R;
--   2. $S$ has a nearly periodic MICP formulation;
--   3. there is a closed convex $\tilde M$ such that $(\tilde M, d-1)$ induces a rational MICP formulation of a nonempty set $\tilde S$ with
--   $$D_{\mathrm{MICP}}(\tilde M) \le D_{\mathrm{MICP}}(M), \qquad S \subseteq \tilde S \subseteq \mathrm{cl}(\tilde S) \subseteq \mathrm{cl}(S).$$
--
--   This is the second key lemma behind Theorem 5.1; option 3 feeds the induction on the number of integer variables.
--
--   **Formalization Note** "$d - 1$" is written via $d = d' + 1$, so option 3 is impossible when $d = 0$ (no truncated subtraction). The number of continuous variables of $\tilde M$ is existential. The nearly periodic formulation in option 2 may be any MICP formulation of $S$, not necessarily rational.
-- source:
--   Lubin, Vielma, Zadik, Mixed-integer convex representability, arXiv:1706.05135v3, p. 22, Lemma 6.2

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

namespace MICPRep.Periodic

open scoped ENNReal Matrix

/-- Lemma 6.2, p. 22. -/
theorem lemma_6_2 {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (hS : S.Nonempty) (hD : micpDiam M < ⊤)
    (hint : (intrinsicInterior ℝ (IZ (indexSet M)) ∩ intLattice d).Nonempty) :
    IsBinaryMICPR S ∨ HasNearlyPeriodicFormulation S ∨
      ∃ d' : ℕ, d = d' + 1 ∧
        ∃ (p' : ℕ) (Mt : Set (Ambient n p' d')) (St : Set (Pt n)),
          IsRationalFormulation Mt St ∧ St.Nonempty ∧ micpDiam Mt ≤ micpDiam M ∧
          S ⊆ St ∧ St ⊆ closure St ∧ closure St ⊆ closure S := by sorry

end MICPRep.Periodic
