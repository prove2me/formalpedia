-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_lemma_4_2
-- name    : IntervalMaxCutEPTAS.Scheme.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:25.65351+00:00
-- url     : https://prove2.me/theorems/cbec754b-146b-46be-af3b-9026faeeb61f
-- title:
--   Lemma 4.2 — a shift with small rejected degree
-- statement:
--   Let $\rho$ be a rank representation of a graph $G$ with $m$ edges, $b\ge4$ an integer and $\sigma=2^{-b}$. There is a shift $\theta\in\{0,\dots,2M-1\}$ whose set $Z_\theta$ of rejected vertices satisfies
--
--   $$\sum_{v\in Z_\theta}\deg_G(v)\le 4\sigma m.$$
--
--   Differences from the source:
--   - encoding: vertex set V(G) of size n → Fin n, with a rank representation ρ (fields l, r, injectivity, range 1..2n, l < r); reason: labelling the vertices 0..n−1 restricts no instance; the structure is exactly §4.1's representation
--   - encoding: σ = 2^{-b} in inequalities → inequalities multiplied out by powers of two in ℕ/ℤ; reason: exact equivalence: σ is an exact power of two, nothing is rounded
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Lemma 4.2, PDF p. 15 (printed p. 14); proof to PDF p. 16

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Hierarchy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

/-- Lemma 4.2: for every rank representation and integer `b ≥ 4` there is a shift
`θ ∈ {0, …, 2M − 1}` with `Σ_{v ∈ Z_θ} deg_G(v) ≤ 4σm` (`σ = 2^{-b}`). -/
theorem lemma_4_2 {n : ℕ} (ρ : RankRep n) (b : ℕ) (hb : 4 ≤ b) :
    ∃ θ : ℕ, θ < 2 * bigM n ∧ GoodShift ⟨ρ, b, θ⟩ := by sorry

end IntervalMaxCutEPTAS.Scheme
