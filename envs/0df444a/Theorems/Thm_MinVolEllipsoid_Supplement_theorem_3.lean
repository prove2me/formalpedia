-- Prove2me | Theorems.Thm_MinVolEllipsoid_Supplement_theorem_3
-- name    : MinVolEllipsoid.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:35:19.660403+00:00
-- url     : https://prove2.me/theorems/64d29686-21ea-4243-8684-f2e155b040f1
-- title:
--   Theorem 3 — $\mathrm{Vol}(\mathcal E_{\mathrm{sdp}})\le\mathrm{Vol}(\mathcal E_{\mathrm{smvie}})$ for polytopes
-- statement:
--   Let $\mathcal P=\{x\in\mathbb R^K:Sx\le t\}$, $S\in\mathbb R^{J\times K}$, $t\in\mathbb R^J$, be a polytope satisfying Assumption 1 (compact, convex, nonempty interior). Then
--
--   $$
--   \mathrm{Vol}(\mathcal E_{\mathrm{sdp}})\le\mathrm{Vol}(\mathcal E_{\mathrm{smvie}}).
--   $$
--
--   Here $\mathcal E_{\mathrm{sdp}}$ is the ellipsoid $\mathcal E(A,b)$ given by an optimal solution of the SDP (12), whose objective $-\log\det(A)=\log\mathrm{Vol}(\mathcal E(A,b))$ under the convention $\mathrm{Vol}(\mathcal E(A,b))=1/\det A$ of p.5, and $\mathcal E_{\mathrm{smvie}}$ is the maximum volume inscribed ellipsoid scaled by the factor $K$, whose log-volume is the optimal value of (28). The statement is therefore
--
--   $$
--   \inf\{-\log\det A:\ (A,b,N,F,g,h)\ \text{feasible for (12)}\}\ \le\ \sup\{\log\det B:\ (B,d)\ \text{feasible for (28)}\}.
--   $$
--
--   The scaled inscribed ellipsoid is a classical outer approximation of the minimum volume circumscribing ellipsoid; the theorem shows the SDP approximation of §3 is never worse.
--
--   **Formalization Note** Both sides are extended-real optimal values (`MinVolEllipsoid.Supplement.logVolSdp` and `MinVolEllipsoid.Supplement.logVolSmvie`), with $A$ and $B$ ranging over positive definite matrices, the domains of $\mp\log\det$. Attainment of the optima is not assumed.
--
--   Differences from the source:
--   - reading: "If 𝒫 is a polytope defined as in (10)" → 𝒫 = {Sx ≤ t} compact, convex, with nonempty interior; reason: Assumption 1 is the paper's standing assumption (p.1, "we focus on sets 𝒫 that satisfy the following assumption"), and ℰ_sdp, ℰ_smvie are defined through it (Appendix B.1 uses an interior point).
--   - reading: Vol(ℰ_sdp) ≤ Vol(ℰ_smvie) for the ellipsoids defined by optimal solutions → the optimal value of (12) is at most the optimal value of (28); reason: by p.11 and p.31 these optimal values are log Vol(ℰ_sdp) and log Vol(ℰ_smvie), and log is increasing; the value form needs no attainment hypothesis.
--   - reading: (11) inside (12) → as in Theorem 2, ⪯ requires −𝒮⊤N𝒮 − [F g; g⊤ h − 1] to be symmetric PSD; reason: the order ⪰ of p.5 is defined on 𝕊ᴷ⁺¹.
--   - encoding: optimal values → EReal infimum and supremum; reason: Lean convention, no junk values; same instances.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Theorem 3, p.11 (proof pp.12–13; (12) p.11; (28) p.31)

import Mathlib
import Definitions.Def_MinVolEllipsoid_Supplement_polytope
import Definitions.Def_MinVolEllipsoid_Supplement_logVolSdp
import Definitions.Def_MinVolEllipsoid_Supplement_logVolSmvie

namespace MinVolEllipsoid.Supplement

/-- **Theorem 3** (Mittal & Hanasusanto, arXiv:1807.07507v4, Theorem 3, p.11).

If `𝒫` is a polytope defined as in (10), then `Vol(ℰ_sdp) ≤ Vol(ℰ_smvie)`.

Stated as the comparison of the logarithms of the two volumes, i.e. of the optimal values that
define them: the optimal value of the SDP (12) (`log Vol(ℰ_sdp) = −log det A` at an optimum, with
`Vol(ℰ(A, b)) = 1/det A`, p.5) is at most the optimal value of (28) (`log Vol(ℰ_smvie)`,
Appendix B.1, p.31).

**Formalization Note** `𝒫 = {x : Sx ≤ t}` is assumed to satisfy Assumption 1 (compact, convex,
full-dimensional), the paper's standing assumption (p.1), under which `ℰ_sdp` and `ℰ_smvie` are
defined. Both sides are `EReal` optimal values (`logVolSdp`, `logVolSmvie`); `log` is increasing, so
the inequality of logarithms is the inequality of volumes. Attainment of the optima is not
assumed. -/
theorem theorem_3 {n m : ℕ} (S : Matrix (Fin m) (Fin n) ℝ) (t : Fin m → ℝ)
    (hPc : IsCompact (polytope S t)) (hPcv : Convex ℝ (polytope S t))
    (hPi : (interior (polytope S t)).Nonempty) :
    logVolSdp S t ≤ logVolSmvie S t := by sorry

end MinVolEllipsoid.Supplement
