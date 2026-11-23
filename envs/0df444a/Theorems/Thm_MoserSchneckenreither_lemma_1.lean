-- Prove2me | Theorems.Thm_MoserSchneckenreither_lemma_1
-- name    : MoserSchneckenreither.lemma_1
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T08:56:47.860821+00:00
-- url     : https://prove2.me/theorems/dce12b43-9f77-42d2-a379-b05ebe5855be
-- title:
--   Lemma 1 — Additivity and monotonicity of potential
-- statement:
--   Fix a finite signature, a relative rewrite problem, and an annotated signature satisfying its constructor-like uniqueness and superposition requirements. For every ground normal form $v$, sharing $p=p_1+p_2$ gives $\Phi(v:p)=\Phi(v:p_1)+\Phi(v:p_2)$, and componentwise $p\le q$ gives $\Phi(v:p)\le\Phi(v:q)$. Both conclusions include the zero annotation and unsupported normal forms.
-- source:
--   Georg Moser and Manuel Schneckenreither, Automated amortised resource analysis for term rewrite systems, Science of Computer Programming 185 (2020), article 102306, https://doi.org/10.1016/j.scico.2019.102306. Section 5, p. 8, Lemma 1.

import Definitions.Def_MoserSchneckenreither_Annotations

namespace MoserSchneckenreither

theorem lemma_1 {sig : Signature} {P : Problem sig} (F : AnnotatedSignature P)
    (v : Term sig) (hv : v.Ground) (hn : Normal P.rules v) :
    (∀ p p₁ p₂ : Annotation, Shares p p₁ p₂ →
      potential F v p = potential F v p₁ + potential F v p₂) ∧
    (∀ p q : Annotation, p ≤ q → potential F v p ≤ potential F v q) := by sorry

end MoserSchneckenreither
