-- Prove2me | Theorems.Thm_HDXNbhdPCP_Main_lemma_6_10
-- name    : HDXNbhdPCP.Main.lemma_6_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:59:58.817853+00:00
-- url     : https://prove2.me/theorems/96a7d45e-8192-4e75-87c0-0a32c0ff07be
-- title:
--   Lemma 6.10 — the nested test in spherical buildings is $(\varepsilon,\eta,2^{-29},7)$-sound
-- statement:
--   Let $1\le a<b<c<d<e<n$ satisfy (6.1): $b>2a$, $c>3a$, $e>2d-a$. There is a polynomial $p_{a,b,c,d,e,n}$ such that for all $\varepsilon,\eta\in(0,1)$, every prime power $q\ge p_{a,b,c,d,e,n}(1/\varepsilon,1/\eta)$ and $V=\mathbb F_q^n$, the neighbourhood test (Definition 3.1) on the regrouped building
--   $$\mathcal X(V)\big[1\mapsto\{a,e\},\ 2\mapsto\{c\},\ 3\mapsto\{b,d\}\big]$$
--   is $(\varepsilon,\eta,2^{-29},7)$-sound.
--
--   This is the local soundness input of the construction (Appendix A), transferred to KMS links in Lemma 6.11.
--
--   Differences from the source:
--   - encoding: q ⩾ poly_{a,b,c,d,e,n}(1/ε, 1/η), a prime power; V an n-dimensional space over F_q → |K| ≥ P₀ (ε⁻¹ η⁻¹)^k for a finite field K, with P₀, k chosen after a, …, n; V = K^n; reason: for x, y ≥ 1 every polynomial is bounded by such a monomial and conversely; finite fields are exactly the F_q
--   - encoding: e > 2d − a → e + a > 2d in ℕ; reason: same condition, avoiding natural-number subtraction
--   - encoding: the regrouped colours 1, 2, 3 and K[{c}] identified with K[c] → Fin 3 colours 0, 1, 2; the colour-2 vertices are {c}-faces (functions on a one-element colour set); reason: canonically isomorphic universes; soundness is invariant under renaming the universe
--   - encoding: a nonempty finite alphabet Σ → a type Sig : Type with Fintype (and Nonempty where the source asks for it); reason: every finite alphabet is in bijection with a type in Type 0
-- source:
--   Dikstein, Dinur, Hopkins, Singer, Sounder, shorter, and simpler PCPs from HDX neighborhoods, STOC 2027 submission (manuscript sha256 7dcb1b53…), p. 41, Lemma 6.10 (proved in Appendix A)

import Mathlib
import Definitions.Def_HDXNbhdPCP_Main_Complex
import Definitions.Def_HDXNbhdPCP_Main_Agreement
import Definitions.Def_HDXNbhdPCP_Main_Building

namespace HDXNbhdPCP.Main

/-- Lemma 6.10: the nested neighbourhood test on `𝒳(V)[1 ↦ {a, e}, 2 ↦ {c}, 3 ↦ {b, d}]` is
`(ε, η, 2^{-29}, 7)`-sound once `q ≥ poly_{a,b,c,d,e,n}(1/ε, 1/η)`. -/
theorem lemma_6_10 (a b c d e n : ℕ) (h1a : 1 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hde : d < e) (hen : e < n) (h61b : b > 2 * a) (h61c : c > 3 * a) (h61e : e + a > 2 * d) :
    ∃ P₀ : ℝ, ∃ k : ℕ, ∀ ε η : ℝ, 0 < ε → ε < 1 → 0 < η → η < 1 →
      ∀ (K : Type) [Field K] [Fintype K], (Fintype.card K : ℝ) ≥ P₀ * (ε⁻¹ * η⁻¹) ^ k →
        (((building K n).regroup
            ![bcolorsOf n {a, e}, bcolorsOf n {c}, bcolorsOf n {b, d}]).nbhdTestOn 0 1 2).IsSound
          ε η (1 / 2 ^ 29) 7 := by sorry

end HDXNbhdPCP.Main
