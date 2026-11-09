-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_lemma_5_1
-- name    : IntervalMaxCutEPTAS.Scheme.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:04.585079+00:00
-- url     : https://prove2.me/theorems/63149f3a-50fd-4e25-89f1-ac54d3f5aa06
-- title:
--   Lemma 5.1 — rounding a set to allowed counts
-- statement:
--   Let $b\ge4$, $\theta\in\{0,\dots,2M-1\}$ and $\gamma\in(0,1)$. For every $S\subseteq V(G)$ there is a set $S'$ with $S'\cap Z=S\cap Z$ such that $S'\setminus Z$ is allowed,
--
--   $$\bigl||S'|-|S|\bigr|\le\gamma n,\qquad \mathrm{cut}_H(S')\ge\mathrm{cut}_H(S)-2\gamma|E(H)|.$$
--
--   Differences from the source:
--   - generalization: the shift θ fixed as in Lemma 4.2 (PDF p. 16) → every shift θ ∈ {0, …, 2M − 1}; reason: the source's proof of this item never uses Lemma 4.2's bound; specializing θ to the fixed shift gives the source statement
--   - encoding: vertex set V(G) of size n → Fin n, with a rank representation ρ (fields l, r, injectivity, range 1..2n, l < r); reason: labelling the vertices 0..n−1 restricts no instance; the structure is exactly §4.1's representation
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Lemma 5.1, PDF p. 19 (printed p. 18)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Tables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

/-- Lemma 5.1: for every `S ⊆ V(G)` there is `S'` with `S' ∩ Z = S ∩ Z`, `S' \ Z` allowed,
`||S'| − |S|| ≤ γn` and `cut_H(S') ≥ cut_H(S) − 2γ|E(H)|`. -/
theorem lemma_5_1 {n : ℕ} (P : Setup n) (hb : 4 ≤ P.b) (hθ : P.θ < 2 * bigM n)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (S : Finset (Fin n)) :
    ∃ S' : Finset (Fin n), S' ∩ Z P = S ∩ Z P ∧ Allowed P γ (S' \ Z P) ∧
      |(S'.card : ℝ) - S.card| ≤ γ * n ∧
      (cutCount (H P) S : ℝ) - 2 * γ * ((H P).edgeFinset.card : ℝ) ≤ cutCount (H P) S' := by sorry

end IntervalMaxCutEPTAS.Scheme
