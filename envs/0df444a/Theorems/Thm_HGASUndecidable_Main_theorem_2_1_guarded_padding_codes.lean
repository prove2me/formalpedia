-- Prove2me | Theorems.Thm_HGASUndecidable_Main_theorem_2_1_guarded_padding_codes
-- name    : HGASUndecidable.Main.theorem_2_1_guarded_padding_codes
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:50:37.501738+00:00
-- url     : https://prove2.me/theorems/78fb8fc9-453d-4fb3-ae9a-ecaf23b65b77
-- title:
--   Guarded computable padding of lifted raw codes
-- statement:
--   Fix source parameters $n_0,k_0\geq1$, a target dimension $n\geq\binom{n_0+k_0-1}{k_0}$, an integer $j\geq0$, and a total computable auxiliary lift $f:\mathbb N\to\mathbb N$. There is a total computable guarded lift-and-pad map $r:\mathbb N\to\mathbb N$ with the following two properties.
--
--   1. If $e$ decodes to a valid source code $c$ of dimension $n_0$ and degree $2k_0+1$, and $f(\operatorname{encode}c)$ decodes to a valid code $(m,3,\mathrm{terms})$, where $m=\binom{n_0+k_0-1}{k_0}$, then $r(e)$ decodes to a valid target code $(n,3+2j,\mathrm{outTerms})$. Its denoted vector field is exactly the Lemma 6.1 padding of the cubic field denoted by $(m,3,\mathrm{terms})$.
--   2. Conversely, whenever the output of $r$ at $e$ decodes to any valid code, the input $e$ decodes to a valid source code of the prescribed dimension and degree.
--
--   Thus $r$ handles invalid and wrong-format inputs without introducing valid positive instances. On successful guarded branches it computes the finite coefficient list representing the explicit polynomial padding $(|x|^2+|z|^2)^j(H(x),-z_1^3,\ldots,-z_{n-m}^3)$. This supplies exactly the coding interface needed to compose Theorem 2.4 with Lemma 6.1.
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), proof of Theorem 2.1 and Lemma 6.1, printed p. 35 (PDF 37); code validity and effective decoding in Section 3.4, printed p. 16 (PDF 18).

import Definitions.Def_HGASUndecidable_Main_Codes

open Filter Topology MeasureTheory
open scoped BigOperators

theorem HGASUndecidable.Main.theorem_2_1_guarded_padding_codes (n₀ k₀ n j : ℕ)
    (hn₀ : 1 ≤ n₀) (hk₀ : 1 ≤ k₀) (hn : Nat.choose (n₀+k₀-1) k₀ ≤ n)
    (f : ℕ → ℕ) (hf : Computable f) :
    ∃ r : ℕ → ℕ, Computable r ∧
      (∀ e c (terms : List (ℕ × List ℕ × ℚ)),
        HGASUndecidable.Main.decodeField e = some c →
        HGASUndecidable.Main.ValidCode c → c.1 = n₀ →
        c.2.1 = 2*k₀+1 →
        HGASUndecidable.Main.decodeField (f (Encodable.encode c)) =
          some (Nat.choose (n₀+k₀-1) k₀, 3, terms) →
        HGASUndecidable.Main.ValidCode (Nat.choose (n₀+k₀-1) k₀, 3, terms) →
        ∃ outTerms : List (ℕ × List ℕ × ℚ),
          HGASUndecidable.Main.decodeField (r e) = some (n, 3+2*j, outTerms) ∧
          HGASUndecidable.Main.ValidCode (n, 3+2*j, outTerms) ∧
          HGASUndecidable.Main.codeField (n, 3+2*j, outTerms) =
            HGASUndecidable.Main.padding hn j
              (HGASUndecidable.Main.codeField
                (Nat.choose (n₀+k₀-1) k₀, 3, terms))) ∧
      (∀ e q, HGASUndecidable.Main.decodeField (r e) = some q →
        HGASUndecidable.Main.ValidCode q →
        ∃ c, HGASUndecidable.Main.decodeField e = some c ∧
          HGASUndecidable.Main.ValidCode c ∧ c.1 = n₀ ∧
          c.2.1 = 2*k₀+1) := by sorry
