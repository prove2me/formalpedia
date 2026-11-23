-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_polynomial_vector_program
-- name    : ITPIRPreproc.MatchVec.polynomial_vector_program
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:40:32.6154+00:00
-- url     : https://prove2.me/theorems/abb42fd3-425d-463e-87c1-321d99ad13d5
-- title:
--   Appendix A — indexed polynomial-vector RAM program with linear workspace
-- statement:
--   There are an injective enumeration $\sigma_a$ of the $2^h$ row words in $[\ell]^\ell$, a bijective enumeration of all polynomial coordinates $(I,\alpha)$, absolute constants $C_0,c_0$, and one deterministic word-RAM program, uniform in $h$, that on input $(h,a)$ outputs the three-bit encodings of
--   $$
--   u_{\sigma_a,I,\alpha}=c_{|I|}\,\mathbf 1[\sigma_a|_I=\alpha],
--   \qquad
--   v_{\sigma_a,I,\alpha}=\mathbf 1[\sigma_a|_I=\alpha].
--   $$
--   For every $h\ge3$, the program uses at most $C_0dh^{c_0}$ work and at most $C_0d$ working bits, where $d$ is the number of coordinates.
--
--   This is the indexed implementation part of Appendix A. The intended enumeration is the first $2^h$ lexicographic words, followed by all $(I,\alpha)$ with $|I|\le k$ in nested mixed-radix order. The coefficients $c_t$ are computed by the paper’s binomial inversion. The coordinate enumeration is deliberately left existential: it is fixed by the algorithm’s own enumeration order, while the statement ensures that the algorithm’s outputs are consistent with that order.
-- source:
--   Dujmovic–Lai–Wichs, STOC 2027 submission #572, Appendix A, printed pp.36–37 (PDF pp.38–39): explicit coordinate formulas, binomial inversion, and “Each entry takes poly(h) time to compute.”

import Definitions.Def_ITPIRPreproc_MatchVec_IndexedVectorComputation
import Definitions.Def_ITPIRPreproc_MatchVec_PolynomialParameters

open ITPIRPreproc.MatchVec ITPIRPreproc.MatchVec.PolynomialConstruction

theorem ITPIRPreproc.MatchVec.polynomial_vector_program :
    ∃ (dim : ℕ → ℕ)
      (rows : ∀ h : ℕ, Fin (2^h) ↪ (Fin (wordLength h) → Fin (wordLength h)))
      (coords : ∀ h : ℕ, Fin (dim h) ≃
        Coordinate (wordLength h) (degree (exponent2 h) (exponent3 h)))
      (C₀ : ℝ) (c₀ : ℕ) (vecProg : WordRAM.Program),
      IndexedVectorComputable dim
        (fun h r j => leftVector (coefficient (wordLength h) (exponent2 h) (exponent3 h))
          (rows h r) (coords h j))
        (fun h r j => rightVector (rows h r) (coords h j))
        C₀ c₀ vecProg := by sorry
