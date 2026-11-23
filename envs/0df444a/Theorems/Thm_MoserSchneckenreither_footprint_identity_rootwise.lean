-- Prove2me | Theorems.Thm_MoserSchneckenreither_footprint_identity_rootwise
-- name    : MoserSchneckenreither.footprint_identity_rootwise
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T08:57:22.202502+00:00
-- url     : https://prove2.me/theorems/e5062ebc-95ee-4805-a6ff-c57e643cf102
-- title:
--   Lemma 2 — Footprint identity for rootwise potential
-- statement:
--   Let $\Gamma\vdash_{\mathrm{fp}}^k t:q$ be a footprint in which every symbol of $t$ is constructor-like. For every total assignment $\sigma$ from variables to terms, the rootwise potential of $t\sigma$ at $q$ equals the sum of the rootwise potentials of the substitution images at their context annotations, plus $k$. The assignment can take open terms as values.
-- source:
--   Georg Moser and Manuel Schneckenreither, Automated amortised resource analysis for term rewrite systems, Science of Computer Programming 185 (2020), article 102306, https://doi.org/10.1016/j.scico.2019.102306. Proposed correction to Lemma 2, pp. 8–9, using a rootwise variation of Definition 3.

import Definitions.Def_MoserSchneckenreither_Typing
import Definitions.Def_MoserSchneckenreither_RootPotential

namespace MoserSchneckenreither

theorem footprint_identity_rootwise {sig : Signature} {P : Problem sig}
    (F : AnnotatedSignature P) {Γ : Context} {k : ℚ≥0} {t : Term sig} {q : Annotation}
    (h : Typing F .footprint Γ k t q) (hs : ∀ f ∈ t.symbols, ConstructorLike P f)
    (σ : ℕ → Term sig) :
    rootPotential F (t.subst σ) q = rootContextPotential F σ Γ + k := by sorry

end MoserSchneckenreither
