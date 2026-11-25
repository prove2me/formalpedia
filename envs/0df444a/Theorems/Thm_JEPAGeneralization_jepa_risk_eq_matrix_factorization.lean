-- Prove2me | Theorems.Thm_JEPAGeneralization_jepa_risk_eq_matrix_factorization
-- name    : JEPAGeneralization.jepa_risk_eq_matrix_factorization
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T04:41:44.332596+00:00
-- url     : https://prove2.me/theorems/d441f5f2-eb7c-4bff-9f82-f3bf489e9a4c
-- title:
--   Theorem 3.1: equivalence between JEPA and matrix factorization
-- statement:
--   Let $w$ be an action-conditioned co-occurrence model on a finite observation space $\mathcal X$ with positive marginals $w(x)$ and $w(x^+\mid a)$, and fix an action $a$. There is a constant $C$, depending only on $w$ and $a$, such that for every encoder $f:\mathcal X\to\mathbb R^k$ and predictor $g:\mathbb R^k\times\mathcal A\to\mathbb R^k$ that are normalized at $a$, i.e. $\|f(x)\|=\|g(f(x),a)\|=1$ for all $x$,
--
--   $$\mathcal R_{\mathrm{JEPA}}(f,g,a)=\big\|\bar M(a)-G(F,a)^\top F\big\|_F^2+C,$$
--
--   where $F=[\sqrt{w(x\mid a)}\,f(x)]_{x\in\mathcal X}$ and $G(F,a)=[\sqrt{w(x)}\,g(f(x),a)]_{x\in\mathcal X}$.
--
--   So, for normalized embeddings, minimizing the JEPA risk with the uniformity term is the same as a low-rank factorization of the normalized co-occurrence matrix.
--
--   **Formalization Note** The paper's "$+\,\mathrm{const.}$" is stated as the existence of one constant $C$ valid for all normalized $(f,g)$. The proof gives $C=2-\sum_{x,x^+}w(x,x^+,a)^2/(w(x)w(x^+\mid a))$.
-- source:
--   Cui, Zhang, Wen, Cheng and Wang, A Generalization Theory for JEPA-Based World Models, arXiv:2606.27014v2 (2026), Section 3.1, Theorem 3.1, eq. (6), p. 4; proof in Appendix A.2, eq. (31)-(32), p. 12

import Mathlib
import Definitions.Def_JEPAGeneralization_Basic

open Finset

namespace JEPAGeneralization

theorem jepa_risk_eq_matrix_factorization {X A : Type*} [Fintype X] {k : ℕ}
    (pX : X → ℝ) (w : X → X → A → ℝ) (hw : IsCoOccurrence pX w) (a : A) :
    ∃ C : ℝ, ∀ (f : X → Fin k → ℝ) (g : (Fin k → ℝ) → A → Fin k → ℝ), IsNormalized f g a →
      jepaRisk pX w f g a = sJepaRisk pX w f g a + C := by sorry

end JEPAGeneralization
