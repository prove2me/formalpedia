-- Prove2me | Theorems.Thm_MarkmanSecant_similarity_of_opposite_annihilator_action
-- name    : MarkmanSecant.similarity_of_opposite_annihilator_action
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T04:25:51.0661+00:00
-- url     : https://prove2.me/theorems/3361c118-4b35-4d13-8cbf-caf272342ac0
-- title:
--   Opposite scalar actions on complementary pure-spinor annihilators give a similarity
-- statement:
--   Let $s,t$ be even pure spinors for $V=\mathbb C^{2n}\oplus(\mathbb C^{2n})^*$, and suppose their annihilators have zero intersection. Let $c\in\mathbb C$ and let $f:V\to V$ be complex linear, acting by $c$ on $\operatorname{ann}(s)$ and by $-c$ on $\operatorname{ann}(t)$. Then $f^2=c^2\operatorname{id}$ and $(f(v),f(w))_V=-c^2(v,w)_V$ for all $v,w$. For $c=\sqrt{-d}$ the multiplier is $d$. The statement also includes $c=0$, when $f=0$.
-- source:
--   Markman, Cycles on abelian 2n-folds of Weil type from secant sheaves on abelian n-folds, arXiv:2502.03415v2, Section 2.2, equation (2.2.4) and the pairing calculation in the proof of Lemma 2.2.4; specialized to opposite eigenvalues, with the square identity made explicit. https://arxiv.org/html/2502.03415v2

import Definitions.Def_MarkmanSecant

open MarkmanSecant

theorem MarkmanSecant.similarity_of_opposite_annihilator_action (n : ℕ) (s t : Spinor n)
    (hs : IsEvenPureSpinor s) (ht : IsEvenPureSpinor t)
    (hst : annih s ⊓ annih t = ⊥) (c : ℂ) (f : VC n →ₗ[ℂ] VC n)
    (hfs : ∀ v ∈ annih s, f v = c • v)
    (hft : ∀ v ∈ annih t, f v = (-c) • v) :
    f ∘ₗ f = c ^ 2 • LinearMap.id ∧
      ∀ v w : VC n, pairV (f v) (f w) = -(c ^ 2) * pairV v w := by sorry
