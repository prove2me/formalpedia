-- Prove2me | Theorems.Thm_FuzzyExtractors_Hamming_syndrome_unique
-- name    : FuzzyExtractors.Hamming.syndrome_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:28.523871+00:00
-- url     : https://prove2.me/theorems/d22198fd-dcbe-4ed8-be7b-1b6e5878fd17
-- title:
--   §5, p. 17 — at most one word within distance $t$ of $w'$ has a given syndrome
-- statement:
--   Let $\mathcal F$ be a finite field and $C\subseteq\mathcal F^n$ a linear code of dimension $k$ in which distinct codewords are at Hamming distance at least $2t+1$. Let $\mathrm{syn}:\mathcal F^n\to\mathcal F^{n-k}$ be a linear map with kernel $C$ (a syndrome map, $\mathrm{syn}(v)=Hv$ for a parity-check matrix $H$). If $v_1,v_2\in\mathcal F^n$ are both within Hamming distance $t$ of $w'$ and have the same syndrome, then
--   $$v_1=v_2 .$$
--
--   This is the correctness argument of the syndrome construction (Construction 3): there can be only one value within distance $t$ of $w'$ whose syndrome is $s$.
--
--   **Formalization Note** The parity-check matrix is replaced by its defining property: any linear map onto $n-k$ coordinates whose kernel is $C$. Minimum distance $2t+1$ is read as "at least $2t+1$".
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, arXiv:cs/0602007v4, §5, p. 17, "There can be only one value within distance t of w′ whose syndrome is s"

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

namespace FuzzyExtractors.Hamming

theorem syndrome_unique {F : Type} [Field F] [Fintype F] [DecidableEq F] {n k t : ℕ}
    (C : Submodule F (Fin n → F)) (hk : Module.finrank F C = k)
    (syn : (Fin n → F) →ₗ[F] (Fin (n - k) → F)) (hsyn : LinearMap.ker syn = C)
    (hdist : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → 2 * t + 1 ≤ hammingDist c c')
    (w' v₁ v₂ : Fin n → F) (h₁ : hammingDist v₁ w' ≤ t) (h₂ : hammingDist v₂ w' ≤ t)
    (hs : syn v₁ = syn v₂) : v₁ = v₂ := by sorry

end FuzzyExtractors.Hamming
