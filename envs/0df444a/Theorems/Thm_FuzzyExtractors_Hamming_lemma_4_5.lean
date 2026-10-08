-- Prove2me | Theorems.Thm_FuzzyExtractors_Hamming_lemma_4_5
-- name    : FuzzyExtractors.Hamming.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:18.076165+00:00
-- url     : https://prove2.me/theorems/51f00b77-3c45-42fc-a17c-4b6d923ed4f1
-- title:
--   Lemma 4.5 — Construction 1 is an average-case $(\mathcal M, m, m-\log|\Pi|+\log\Gamma+\log K, t)$-secure sketch
-- statement:
--   Let $\mathcal M$ be a finite space with a symmetric distance $\mathrm{dis}$, and let $C\subseteq\mathcal M$ be a nonempty $(\mathcal M,K,t)$-code, $K=|C|$: every point has at most one codeword within distance $t$. Let $\Pi$ be a finite family of permutations of $\mathcal M$ that are isometries, $\mathrm{dis}(\pi(a),\pi(b))=\mathrm{dis}(a,b)$, and act transitively: for all $a,b$ some $\pi\in\Pi$ has $\pi(a)=b$. Let $\Gamma\ge 1$ be such that for every $w$ and $b$ there are at least $\Gamma$ permutations $\pi\in\Pi$ with $\pi(w)=b$.
--
--   Let $(\mathsf{SS},\mathsf{Rec})$ be Construction 1: $\mathsf{SS}(w)$ picks $b\in C$ uniformly, then $\pi$ uniformly among the $\pi\in\Pi$ with $\pi(w)=b$, and outputs $\pi$; $\mathsf{Rec}(w',\pi)$ decodes $\pi(w')$ to a codeword $b'$ and outputs $\pi^{-1}(b')$. Then for every $m$,
--   $$(\mathsf{SS},\mathsf{Rec}) \text{ is an average-case } \big(\mathcal M,\; m,\; m-\log|\Pi|+\log\Gamma+\log K,\; t\big)\text{-secure sketch.}$$
--
--   This is the general sketch for transitive metric spaces; the code-offset construction for the Hamming metric is its instance with $\Pi$ the translations.
--
--   **Formalization Note** The page defines $\Gamma$ by the garbled sentence "Let $\Gamma$ be the number of elements $\pi\in\Pi$ such that $\min_{w,b}|\{\pi\mid\pi(w)=b\}|\ge\Gamma$", glossed as "for each $w$ and $b$, there are at least $\Gamma$ choices for $\pi$"; we state the gloss, with $\Gamma>0$ explicit (the paper leaves it implicit in $\log\Gamma$). Symmetry of $\mathrm{dis}$ (a metric axiom the paper assumes for $\mathcal M$) is stated as a hypothesis because decoding uses $\mathrm{dis}(\pi(w'),c)\le t$. "Closest codeword" is replaced by "a codeword within distance $t$", which coincides with it whenever correctness is in question. The efficiency sentence is dropped.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, arXiv:cs/0602007v4, Construction 1 and Lemma 4.5, p. 14

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

namespace FuzzyExtractors.Hamming

theorem lemma_4_5 {M Pm : Type} [Fintype M] [DecidableEq M] [Fintype Pm]
    (dis : M → M → ℕ) (hsymm : ∀ a b, dis a b = dis b a)
    (C : Finset M) (hC : C.Nonempty) (t : ℕ) (hcode : IsCode dis C t)
    (act : Pm → M ≃ M) (hiso : ∀ π a b, dis (act π a) (act π b) = dis a b)
    (htrans : ∀ a b, ∃ π, act π a = b)
    (Γ : ℕ) (hΓpos : 0 < Γ) (hΓ : ∀ w b, Γ ≤ (Finset.univ.filter fun π => act π w = b).card) :
    ∀ m : ℝ, IsAvgSecureSketch dis m
      (m - Real.logb 2 (Fintype.card Pm) + Real.logb 2 Γ + Real.logb 2 C.card) t
      (transSS C hC act htrans) (transRec dis C t act) := by sorry

end FuzzyExtractors.Hamming
