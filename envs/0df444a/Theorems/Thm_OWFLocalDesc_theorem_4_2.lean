-- Prove2me | Theorems.Thm_OWFLocalDesc_theorem_4_2
-- name    : OWFLocalDesc.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:45:02.7061+00:00
-- url     : https://prove2.me/theorems/2d54cd5f-9141-4832-8468-3b7c4e61430a
-- title:
--   Theorem 4.2 (Conditional entropy-preserving generation, cited from Liu–Pass)
-- statement:
--   Assume one-way functions exist. Then there are constants $\alpha>0$ and $0<\xi<1$, a polynomial-time generator $\overline G$ which maps every $r$-bit seed to a string of length $\ell(r)$, where $\ell(r)$ is $r+r^\xi$ rounded to an integer, and nonempty events $E_r\subseteq\{0,1\}^r$ for all sufficiently large $r$, such that:
--
--   1. the first $r$ bits of $\overline G(U_r\mid E_r)$ have Shannon entropy at least $r-\alpha\log r$;
--   2. for every PPT distinguisher given $1^r$ and the challenge, its distinguishing advantage between $\overline G(U_r\mid E_r)$ and a uniform string of length $\ell(r)$ is eventually at most $1/40$.
--
--   Here $U_r\mid E_r$ is a uniform seed conditioned to lie in $E_r$; the events need not be efficiently recognizable or samplable. This is the generator from which the hardness proof (Theorem 4.5) builds planted labels with short certificates and nearly full entropy.
--
--   **Formalization Note** A distinguisher accepts when the first bit of its output is $1$; its advantage is the absolute difference of the two acceptance probabilities.
--
--   Differences from the source:
--   - reading: output length r + r^ξ rounded to an integer (we use only that it is at least r + r^ξ − 1) → |ℓ(r) − (r + r^ξ)| < 1 for every r; reason: the rounding is not specified; this covers floor, ceiling and nearest, and implies ℓ(r) ≥ r + r^ξ − 1
--   - encoding: a polynomial-time generator Ḡ_r with seed length r; distinguishers given 1^r and the challenge; entropy of a conditioned output → one `CookPvsNP.PolyTimeComputable` map G on all strings with |G(u)| = ℓ(|u|); PPT tests on the code of (1^r, challenge); `imageEntropy` over E_r; reason: fixed codes and the standard models; no instance changes
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Theorem 4.2, p.17 (cited from [LP25, Definition A.1 and Lemma A.3])

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_PPT
import Definitions.Def_OWFLocalDesc_OWFExist
import Definitions.Def_OWFLocalDesc_imageEntropy
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Theorem 4.2 (Conditional entropy-preserving generation), cited from [LP25].**
Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Theorem 4.2, p.17: "Assume one-way functions exist. There are
constants α > 0 and 0 < ξ < 1 with the following properties [LP25, Definition A.1 and Lemma A.3].
There is a polynomial-time generator \overline{G}_r with seed length r and output length r + r^ξ
rounded to an integer; we use only that this length is at least r + r^ξ − 1. There are nonempty
events E_r ⊆ {0,1}^r for all sufficiently large r. The first r bits of \overline{G}_r(U_r|E_r) have
entropy at least r − α log r. For every PPT distinguisher given 1^r and the challenge, its
distinguishing advantage between \overline{G}_r(U_r|E_r) and a uniform output of the same length is
eventually at most 1/40."

**Formalization Note.** The generator is one polynomial-time map `G` on all strings, with output
length `ℓ(|seed|)`; "rounded to an integer" is `|ℓ(r) − (r + r^ξ)| < 1` (floor, ceiling or
nearest). The events need not be efficiently recognizable (p.17). Entropy is Shannon entropy in
bits of the first `r` output bits for a seed uniform on `E_r`. A distinguisher is a PPT test on
the code of `(1^r, challenge)`; it accepts when its first output bit is `1`. -/
theorem theorem_4_2 (hOWF : OWFExist) :
    ∃ α ξ : ℝ, 0 < α ∧ 0 < ξ ∧ ξ < 1 ∧
      ∃ (G : List Bool → List Bool) (ℓ : ℕ → ℕ) (E : (r : ℕ) → Finset (Fin r → Bool)) (r₀ : ℕ),
        CookPvsNP.PolyTimeComputable G ∧
        (∀ u : List Bool, (G u).length = ℓ u.length) ∧
        (∀ r : ℕ, |(ℓ r : ℝ) - ((r : ℝ) + (r : ℝ) ^ ξ)| < 1) ∧
        (∀ r ≥ r₀, (E r).Nonempty ∧
          (r : ℝ) - α * Real.logb 2 r ≤ imageEntropy (E r) (fun e => (G (List.ofFn e)).take r)) ∧
        ∀ T : PPT, ∃ r₁ : ℕ, ∀ r ≥ max r₀ r₁,
          |(∑ e ∈ E r, T.prob (QuantumPRC.tupleCode [QuantumPRC.unary r, G (List.ofFn e)]) Accepts) /
              ((E r).card : ℝ) -
            (∑ u : Fin (ℓ r) → Bool,
                T.prob (QuantumPRC.tupleCode [QuantumPRC.unary r, List.ofFn u]) Accepts) /
              (2 : ℝ) ^ (ℓ r)| ≤ 1 / 40 := by sorry

end OWFLocalDesc
