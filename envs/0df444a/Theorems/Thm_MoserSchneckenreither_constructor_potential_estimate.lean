-- Prove2me | Theorems.Thm_MoserSchneckenreither_constructor_potential_estimate
-- name    : MoserSchneckenreither.constructor_potential_estimate
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T08:58:38.010422+00:00
-- url     : https://prove2.me/theorems/aac6450d-bd92-4b77-8fad-ed75f78243fc
-- title:
--   Theorem 7 — A polynomial estimate for ground constructor potential
-- statement:
--   Under the stated polynomial constructor conditions, the whole-term potential of any ground constructor term $v$ at annotation $q$ is at most $\max(q)\,|v|^{\deg(q)}$. The zero annotation has potential zero by homogeneity. The estimate concerns the constructor-potential portion of Theorem 7.
-- source:
--   Georg Moser and Manuel Schneckenreither, Automated amortised resource analysis for term rewrite systems, Science of Computer Programming 185 (2020), article 102306, https://doi.org/10.1016/j.scico.2019.102306. Constructor-potential portion of Theorem 7, pp. 11–12. Nonzero vectors satisfy the strict degree-drop clause and homogeneity handles zero.

import Definitions.Def_MoserSchneckenreither_Typing

namespace MoserSchneckenreither

theorem constructor_potential_estimate {sig : Signature} {P : Problem sig}
    (F : AnnotatedSignature P) (hp : PolynomialConstructors F) (v : Term sig)
    (q : Annotation) (hg : v.Ground) (hv : v.Constructor) :
    potential F v q ≤ q.maxCoeff * (v.size : ℚ≥0) ^ q.degree := by sorry

end MoserSchneckenreither
