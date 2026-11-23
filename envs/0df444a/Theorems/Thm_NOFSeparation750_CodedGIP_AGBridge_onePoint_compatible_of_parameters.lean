-- Prove2me | Theorems.Thm_NOFSeparation750_CodedGIP_AGBridge_onePoint_compatible_of_parameters
-- name    : NOFSeparation750.CodedGIP.AGBridge.onePoint_compatible_of_parameters
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:54:59.806743+00:00
-- url     : https://prove2.me/theorems/31003303-0739-4d21-b5ac-0406ba044eca
-- title:
--   Compatible codes from one-point Goppa bounds
-- statement:
--   Let $\mathbb F$ be a finite field, $K/\mathbb F$ a function field, $P$ a global place, and $E:K\to\mathbb F^r$ a unital multiplicative linear evaluation map. For natural numbers $A,B,g,s$, put $V=E(L(AP))$ and $W=E(L(BP))$.
--
--   Assume $k,r\ge1$, $s\ge6$, $kA\le B$, $A\ge3$, and $4(B+1)\le r$, together with
--   $$
--   \frac{8r}{s}\le A+1,\qquad A+g\le\dim_{\mathbb F}V,\qquad r-B+1\le d(W).
--   $$
--   If $W$ is nonzero, then $V,W$ are $(6/s,3/4)$-compatible for $k$-products.
--
--   This isolates the generic one-point algebraic-geometry argument: multiplicative evaluation sends $k$-products from $L(AP)$ into $L(kAP)$, while the numerical hypotheses convert the dimension and designed-distance bounds into the required rates. It is independent of any particular Garcia–Stichtenoth tower.
-- source:
--   Wang–Wang–Wu, STOC 2027 submission #750, Appendix A.1 equations (A.2)–(A.3) p.11 and Appendix A.3 Construction, Products, and Distance and dimension, pp.12–13.

import Definitions.Def_NOFSeparation750_CodedGIP_AGBridge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators WithZero
noncomputable section
open NOFSeparation750.CodedGIP.AGBridge

theorem NOFSeparation750.CodedGIP.AGBridge.onePoint_compatible_of_parameters
    {F : Type} [Field F] [Finite F] {K : Type*} [Field K] [Algebra F K] {r : ℕ}
    (E : K →ₗ[F] (Fin r → F)) (hone : E 1 = 1)
    (hmul : ∀ x y, E (x * y) = E x * E y) (P : GlobalPlace F K)
    (k A B g s : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (hs : 0 < s) (h6s : 6 ≤ s)
    (hW : rrEvaluationCode E (poleDivisor P B) ≠ ⊥) (hkA : k * A ≤ B)
    (hA3 : 3 ≤ A)
    (hA : 8 * (r : ℝ) / (s : ℝ) ≤ ((A + 1 : ℕ) : ℝ))
    (hB : 4 * (B + 1) ≤ r)
    (hdimQEC : A + g ≤ Module.finrank F (rrEvaluationCode E (poleDivisor P A)))
    (hdistQEC : r - B + 1 ≤
      NOFSeparation750.CodedGIP.distance (rrEvaluationCode E (poleDivisor P B))) :
    NOFSeparation750.CodedGIP.Compatible
      (rrEvaluationCode E (poleDivisor P A)) (rrEvaluationCode E (poleDivisor P B))
      k (6 / (s : ℝ)) (3 / 4) := by sorry
