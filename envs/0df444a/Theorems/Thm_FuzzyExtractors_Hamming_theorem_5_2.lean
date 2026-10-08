-- Prove2me | Theorems.Thm_FuzzyExtractors_Hamming_theorem_5_2
-- name    : FuzzyExtractors.Hamming.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:17.077001+00:00
-- url     : https://prove2.me/theorems/515bc82a-ddb4-43dd-9921-961e16391aa9
-- title:
--   Theorem 5.2 — every $[n,k,2t+1]_{\mathcal F}$ code gives an average-case fuzzy extractor with $\ell=m+kf-nf-2\log(1/\varepsilon)+2$
-- statement:
--   Let $\mathcal F$ be a finite additive group with $F=|\mathcal F|$ elements, $f=\log F$, and let $\mathcal M=\mathcal F^n$ with the Hamming distance. Let $C\subseteq\mathcal F^n$ be a nonempty code with $K$ codewords in which distinct codewords are at Hamming distance at least $2t+1$, and write $kf=\log K$. Let $m$ be real, $\varepsilon>0$, and let $\ell$ be a natural number with
--   $$\ell\;\le\;m+kf-nf-2\log(1/\varepsilon)+2 .$$
--   Then there exists an average-case $(\mathcal F^n,m,\ell,t,\varepsilon)$-fuzzy extractor: procedures $\mathsf{Gen}$, producing an $\ell$-bit string $R$ and a helper string $P$ from $w$, and $\mathsf{Rep}$, such that $\mathsf{Rep}(w',P)=R$ whenever $w'$ is within Hamming distance $t$ of $w$, and
--   $$\mathbf{SD}\big((R,P,I),(U_\ell,P,I)\big)\le\varepsilon$$
--   for every pair $(W,I)$ with $\tilde{\mathbf H}_\infty(W\mid I)\ge m$.
--
--   This is the paper's fuzzy extractor for the Hamming metric: the key length loses only the redundancy $(n-k)f$ of the code and the unavoidable $2\log(1/\varepsilon)$.
--
--   **Formalization Note** The paper writes $\ell = m+kf-nf-2\log(1/\varepsilon)+2$, a real number; since $R$ is an $\ell$-bit string, we state the claim for every natural $\ell$ up to that value, which is the printed claim when the value is a natural number (Lemma 4.3, used in the proof, is phrased the same way). The paper leaves $\varepsilon>0$ implicit in $\log(1/\varepsilon)$; we state it. $kf=\log K$ covers non-linear codes. $\mathcal F$ may be any finite additive commutative group. The efficiency sentence is dropped. The universal hash family is not a hypothesis: its existence is part of the claim.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, arXiv:cs/0602007v4, Theorem 5.2, p. 17

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

namespace FuzzyExtractors.Hamming

theorem theorem_5_2 {F : Type} [Fintype F] [DecidableEq F] [AddCommGroup F] {n : ℕ}
    (C : Finset (Fin n → F)) (hC : C.Nonempty) (t : ℕ) (hdist : MinDistGe C (2 * t + 1))
    (m ε : ℝ) (hε : 0 < ε) (ℓ : ℕ)
    (hℓ : (ℓ : ℝ) ≤ m + Real.logb 2 C.card - (n : ℝ) * Real.logb 2 (Fintype.card F)
      - 2 * Real.logb 2 (1 / ε) + 2) :
    ∃ (P : Type) (Gen : (Fin n → F) → PMF ((Fin ℓ → Bool) × P))
      (Rep : (Fin n → F) → P → PMF (Fin ℓ → Bool)),
      IsAvgFuzzyExtractor hammingDist m ℓ t ε Gen Rep := by sorry

end FuzzyExtractors.Hamming
