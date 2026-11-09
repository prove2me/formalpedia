-- Prove2me | Theorems.Thm_HammingSumset729_Approximation_lemma_A_5
-- name    : HammingSumset729.Approximation.lemma_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:41:58.147342+00:00
-- url     : https://prove2.me/theorems/4afbc7b7-367c-4579-9ba3-14daf9008341
-- title:
--   Lemma A.5 — encoding preserves distances with offset
-- statement:
--   Let $\ell>0$ and $m_1\ge m_2\ge1$, and let $|T'|=m_1\ell$, $|P|=m_2\ell$. Write $\{S\}_{\ell}$ for the concatenation, in residue order, of the subsequences at positions congruent modulo $\ell$. Use distinct fresh symbols $\#$ and $\$$ outside the input alphabet, and construct
--
--   $$T^*=\{T'\}_{\ell}\{T'[\ell\ldots m_1\ell-1]\#^{\ell}\}_{\ell},\qquad
--   P^*=\{P\$^{(m_1-m_2)\ell}\}_{\ell}.$$
--
--   For $0\le\alpha\le(m_1-m_2)\ell$, put $\beta=\lfloor\alpha/\ell\rfloor+(\alpha\bmod\ell)m_1$. Then
--
--   $$\operatorname{HD}(T'[\alpha\ldots\alpha+m_2\ell-1],P)
--   =\operatorname{HD}(T^*[\beta\ldots\beta+m_1\ell-1],P^*)-(m_1-m_2)\ell.$$
--
--   The subtraction is in integers. This fixes the actual padding offset used by the bounded-distance kernel.
--
--   Differences from the source:
--   - encoding: the padded nonempty strings in the small-period branch and a subtracted padding offset → positive ℓ and m₂, m₂≤m₁, actual column/padding constructions and integer subtraction; reason: the positive lengths follow from ℓ≤k≤|P|; integer subtraction preserves the exact offset (m₁−m₂)ℓ
--   - generalization: T′ and P arise in the trimmed small-period branch of Appendix A → any strings with lengths m₁ℓ and m₂ℓ, with ℓ>0 and m₁≥m₂≥1; reason: the rearrangement identity uses only these lengths and the displayed padding constructions; the source strings satisfy every retained hypothesis
-- source:
--   Nick Fischer, Yael Kirkpatrick, Vassilios Nakos, STOC 2027 submission #729 (October 2026), Lemma A.5, printed p. 24 (PDF p. 26). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/729.pdf

import Definitions.Def_HammingSumset729_Approximation_Strings

set_option autoImplicit false
open scoped ENNReal NNReal

namespace HammingSumset729.Approximation

theorem lemma_A_5 {α : Type*} [DecidableEq α] (t p : List α)
    (m₁ m₂ ell : ℕ) (hell : 0 < ell) (hm₂ : 0 < m₂) (hm : m₂ ≤ m₁)
    (ht : t.length = m₁ * ell) (hp : p.length = m₂ * ell)
    (alpha : ℕ) (halpha : alpha ≤ (m₁ - m₂) * ell) :
    (shiftDistance t p alpha : ℤ) =
      (shiftDistance (encodedText t ell) (encodedPattern p t.length ell)
        (alpha / ell + alpha % ell * m₁) : ℤ) - ((m₁ : ℤ) - m₂) * ell := by sorry

end HammingSumset729.Approximation
