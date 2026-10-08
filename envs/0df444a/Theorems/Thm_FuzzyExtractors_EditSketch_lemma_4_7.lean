-- Prove2me | Theorems.Thm_FuzzyExtractors_EditSketch_lemma_4_7
-- name    : FuzzyExtractors.EditSketch.lemma_4_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:22.196571+00:00
-- url     : https://prove2.me/theorems/29d704c9-331a-4be9-bf74-d20900180745
-- title:
--   Lemma 4.7 — a biometric embedding with recovery information transfers average-case secure sketches
-- statement:
--   Let $\mathcal M_1, \mathcal M_2$ be spaces with integer distances $\mathrm{dis}_1, \mathrm{dis}_2$. Let $f : \mathcal M_1 \to \mathcal M_2$ be a $(t_1, t_2, \lambda)$-biometric embedding with recovery information $g$, and let $(\mathsf{SS}, \mathsf{Rec})$ be an average-case $(\mathcal M_2, m_1 - \lambda, \tilde m_2, t_2)$ secure sketch. Define
--   $$\mathsf{SS}'(w) = (\mathsf{SS}(f(w)), g(w)),$$
--   and let $\mathsf{Rec}'(w', (s, r))$ compute $\mathsf{Rec}(f(w'), s)$ to obtain $f(w)$ and then invert $(f(w), r)$ to obtain $w$. Then $(\mathsf{SS}', \mathsf{Rec}')$ is an average-case $(\mathcal M_1, m_1, \tilde m_2, t_1)$ secure sketch.
--
--   This lemma moves secure sketches across metric spaces: Theorem 7.5 applies it with shingling as $f$ and PinSketch as $(\mathsf{SS}, \mathsf{Rec})$.
--
--   **Formalization Note.** The paper prints "computing $\mathsf{Rec}(w', s)$ to get $f(w)$"; $\mathsf{Rec}$ acts on $\mathcal M_2$, so it is read as $\mathsf{Rec}(f(w'), s)$. Inverting $(y, r)$ chooses the $w$ with $f(w) = y$ and $g(w) = r$, which is unique by Definition 7; if no such $w$ exists, $w'$ is returned (this case does not arise under correctness). The paper's proof treats only the worst-case entropy hypothesis; the average-case statement, which is what the lemma asserts, is stated. $\lambda$ is real, and "range size at most $2^\lambda$" is the existence of a finite set of at most $2^\lambda$ elements containing every value of $g$. No metric axioms or finiteness are assumed.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, Lemma 4.7, p. 15

import Mathlib
import Definitions.Def_FuzzyExtractors_EditSketch_Basic

namespace FuzzyExtractors.EditSketch

theorem lemma_4_7 {M₁ M₂ G S : Type} (dis₁ : M₁ → M₁ → ℕ) (dis₂ : M₂ → M₂ → ℕ)
    (t₁ t₂ : ℕ) (lam m₁ m₂' : ℝ) (f : M₁ → M₂) (g : M₁ → G)
    (SS : M₂ → PMF S) (Rec : M₂ → S → PMF M₂)
    (hf : IsEmbeddingWithRecovery dis₁ dis₂ t₁ t₂ lam f g)
    (hSS : FuzzyExtractors.Hamming.IsAvgSecureSketch dis₂ (m₁ - lam) m₂' t₂ SS Rec) :
    FuzzyExtractors.Hamming.IsAvgSecureSketch dis₁ m₁ m₂' t₁ (embedSketch f g SS) (embedRec f g Rec) := by sorry

end FuzzyExtractors.EditSketch
