-- Prove2me | Theorems.Thm_GaussianGLOCC_tmss_degrade_cm
-- name    : GaussianGLOCC.tmss_degrade_cm
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:25:34.873421+00:00
-- url     : https://prove2.me/theorems/7892d8fd-5871-4e63-b2ff-58f0a71ad856
-- title:
--   Eqs. (20)–(21): a unilateral Gaussian operation degrading a TMSS from $r$ to $r'<r$
-- statement:
--   Let $0\le r'<r$ and put
--
--   $$
--   q=\frac{\cosh(r)\cosh(r')-1}{\cosh(r)-\cosh(r')} .
--   $$
--
--   Then
--
--   1. $q\ge 1$;
--   2. there is exactly one $r''\ge 0$ with $\cosh(r'')=q$ (eq. (21));
--   3. for this $r''$, the unilateral Gaussian operation in $A$ with covariance matrix $\Gamma_A=\gamma_{r''}=\begin{pmatrix}A_{r''}&C_{r''}\\C_{r''}&A_{r''}\end{pmatrix}$ (eq. (20)), $A_{r''}=\cosh(r'')\mathbb 1$, $C_{r''}=\sinh(r'')\Lambda$, maps the covariance matrix $\gamma_r$ of a TMSS with parameter $r$ to $\gamma_{r'}$ through the formulas (19a)–(19c).
--
--   This is the single-pair building block of the sufficiency part of Theorem 1.
--
--   Differences from the source:
--   - encoding: the squeezing parameter r″ ∈ [0, ∞) is defined via (21) → explicit clauses q ≥ 1 and ∃! r″ ≥ 0 with cosh r″ = q, and the CM identity for that r″; reason: the definition of r″ presupposes both clauses; stating them makes it well posed
--   - reading: this transformation can be achieved on the level of covariance matrices by the operation with CM Γ_A → unilateralCM (normalForm ![r″]) (normalForm ![r]) = normalForm ![r′]; reason: (19a)–(19c) applied to Γ_A of (20) and γ_r of (3)
-- source:
--   Giedke–Eisert–Cirac–Plenio, Entanglement transformations of pure Gaussian states, arXiv:quant-ph/0301038v1, eqs. (20)–(21), p.6

import Mathlib
import Definitions.Def_GaussianGLOCC_Unilateral
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov FockIndex DensityKernel GaussianWithCovariance)

namespace GaussianGLOCC

/-- Giedke–Eisert–Cirac–Plenio, arXiv:quant-ph/0301038v1, eqs. (20)–(21), p.6: "the unilateral
transformation that transforms a TMSS with squeezing parameter r into another TMSS with squeezing
parameter r′ < r […] is associated with a 4 × 4 CM Γ_A, which is given by Γ_A = [[A_{r″}, C_{r″}],
[C_{r″}, A_{r″}]], (20) where as before A_{r″} = cosh(r″)𝟙 and C_{r″} = sinh(r″)Λ. The squeezing
parameter r″ ∈ [0, ∞) is defined via cosh(r″) = (cosh(r) cosh(r′) − 1)/(cosh(r) − cosh(r′)). (21)"

For `0 ≤ r′ < r`:
1. the right-hand side `q` of (21) satisfies `q ≥ 1`;
2. there is exactly one `r″ ≥ 0` with `cosh r″ = q`;
3. for that `r″`, the unilateral map (19) with `Γ_A = γ_{r″}` sends `γ_r` to `γ_{r′}`, where
   `γ_s = [[cosh(s)𝟙, sinh(s)Λ], [sinh(s)Λ, cosh(s)𝟙]]` is the CM (3) of a TMSS.

**Formalization Note.** `γ_s` is `normalForm ![s]` (one pair, A = mode 0, B = mode 1) and the
map is `unilateralCM` (eqs. (19a)–(19c), (8)). -/
theorem tmss_degrade_cm (r r' : ℝ) (hr' : 0 ≤ r') (hlt : r' < r) :
    1 ≤ (Real.cosh r * Real.cosh r' - 1) / (Real.cosh r - Real.cosh r') ∧
    (∃! r'' : ℝ, 0 ≤ r'' ∧
      Real.cosh r'' = (Real.cosh r * Real.cosh r' - 1) / (Real.cosh r - Real.cosh r')) ∧
    ∀ r'' : ℝ, 0 ≤ r'' →
      Real.cosh r'' = (Real.cosh r * Real.cosh r' - 1) / (Real.cosh r - Real.cosh r') →
      unilateralCM (normalForm ![r'']) (normalForm ![r]) = normalForm ![r'] := by sorry

end GaussianGLOCC
