-- Prove2me | Theorems.Thm_HDXNbhdPCP_Main_lemma_6_11
-- name    : HDXNbhdPCP.Main.lemma_6_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:59:48.608637+00:00
-- url     : https://prove2.me/theorems/e425c80a-7f9b-4398-8646-d54a0861be53
-- title:
--   Lemma 6.11 — the nested test in KMS links is $(\varepsilon,\eta,2^{-35},7)$-sound
-- statement:
--   Fix integers $3<a<b<c<d<e\le n$ with $b>2a-1$, $c>3a-2$, $e>2d-a$. There is a polynomial $p_{a,b,c,d,e,n}$ such that for every $s\ge n$, all $\varepsilon,\eta\in(0,1)$ and every prime power $q\ge p_{a,b,c,d,e,n}(\varepsilon^{-1},\eta^{-1})$, putting $A=A_{q,n,s}$: for every vertex or edge $\tau$ of $A[1,2,3]$, the neighbourhood test on
--   $$A_\tau\big[1\mapsto\{a,e\},\ 2\mapsto\{c\},\ 3\mapsto\{b,d\}\big]$$
--   is $(\varepsilon,\eta,2^{-35},7)$-sound.
--
--   It supplies the local soundness hypothesis of Theorem 3.2 for the KMS complex.
--
--   Differences from the source:
--   - encoding: q ⩾ poly_{a,b,c,d,e,n}(1/ε, 1/η), a prime power; V an n-dimensional space over F_q → |K| ≥ P₀ (ε⁻¹ η⁻¹)^k for a finite field K, with P₀, k chosen after a, …, n; V = K^n; reason: for x, y ≥ 1 every polynomial is bounded by such a monomial and conversely; finite fields are exactly the F_q
--   - encoding: b > 2a − 1, c > 3a − 2, e > 2d − a → b + 1 > 2a, c + 2 > 3a, e + a > 2d in ℕ; reason: same conditions, avoiding natural-number subtraction
--   - encoding: A = A_{q,n,s}; vertices or edges τ of A[1, 2, 3] → kms K n μ for every irreducible μ of degree s; τ = y_J for a facet y and J ⊆ {1, 2, 3} with |J| ∈ {1, 2}; A_τ = A conditioned on x_J = y_J; reason: every vertex or edge of A[1, 2, 3] is such a y_J
--   - encoding: the regrouped colours 1, 2, 3 → Fin 3 colours 0, 1, 2 (colours of A are Fin (n+1)); reason: Lean convention; same instances
--   - encoding: a nonempty finite alphabet Σ → a type Sig : Type with Fintype (and Nonempty where the source asks for it); reason: every finite alphabet is in bijection with a type in Type 0
-- source:
--   Dikstein, Dinur, Hopkins, Singer, Sounder, shorter, and simpler PCPs from HDX neighborhoods, STOC 2027 submission (manuscript sha256 7dcb1b53…), p. 41, Lemma 6.11 (proved pp. 42-43)

import Mathlib
import Definitions.Def_HDXNbhdPCP_Main_Complex
import Definitions.Def_HDXNbhdPCP_Main_Agreement
import Definitions.Def_HDXNbhdPCP_Main_Building

open Polynomial

namespace HDXNbhdPCP.Main

/-- Lemma 6.11: the nested test in the links of vertices and edges of `A[1, 2, 3]`,
`A = A_{q,n,s}`, is `(ε, η, 2^{-35}, 7)`-sound once `q ≥ poly_{a,b,c,d,e,n}(1/ε, 1/η)`. -/
theorem lemma_6_11 (a b c d e n : ℕ) (h3a : 3 < a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hde : d < e) (hen : e ≤ n) (hb : b + 1 > 2 * a) (hc : c + 2 > 3 * a) (he : e + a > 2 * d) :
    ∃ P₀ : ℝ, ∃ k : ℕ, ∀ s : ℕ, n ≤ s → ∀ ε η : ℝ, 0 < ε → ε < 1 → 0 < η → η < 1 →
      ∀ (K : Type) [Field K] [Fintype K], (Fintype.card K : ℝ) ≥ P₀ * (ε⁻¹ * η⁻¹) ^ k →
      ∀ (mu : K[X]) (hmu : Irreducible mu), mu.natDegree = s →
      ∀ J : Finset (Fin (n + 1)), J ⊆ fcolorsOf n {1, 2, 3} → 1 ≤ J.card → J.card ≤ 2 →
      ∀ y ∈ (kms K n mu hmu.ne_zero).supp,
        ((((kms K n mu hmu.ne_zero).condFace J y).regroup
            ![fcolorsOf n {a, e}, fcolorsOf n {c}, fcolorsOf n {b, d}]).nbhdTestOn 0 1 2).IsSound
          ε η (1 / 2 ^ 35) 7 := by sorry

end HDXNbhdPCP.Main
