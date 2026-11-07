-- Prove2me | Theorems.Thm_LowAccLTC_claim_5_8_kms_agreement
-- name    : LowAccLTC.claim_5_8_kms_agreement
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:39:41.624791+00:00
-- url     : https://prove2.me/theorems/c4af94c1-9c17-43eb-a3c3-672f7634dce0
-- title:
--   Claim 5.8 — KMS codes are $(\tau,\ x\mapsto801x/\tau)$-agreement testable w.r.t. the $j$-test
-- statement:
--   In the setting of §5.2 — $0<\varepsilon<1/2$, $p$ prime, $r,m,d\in\mathbb N$ with $r\ge10^{2765}\varepsilon^{-1095}\log^{182}(1/\varepsilon)$, $p\ge10^{485}r^6\varepsilon^{-156}\log^{26}(1/\varepsilon)$ and $d\le p\varepsilon^2/(1000r)$, $X=X(p,r,m)$ for an irreducible $\phi\in\mathbb F_p[t]$ of degree $m$ with $\phi(0)\ne0$, $C=C(p,r,d,m)$, $j=\lceil10^{15}\varepsilon^{-6}\log(1/\varepsilon)\rceil$ and $\tau=1/(10^{23}(2j)^7+10)$ — the KMS code $C$ is
--   $$\Big(\tau,\ x\mapsto\frac{801x}{\tau}\Big)\text{-agreement testable}$$
--   w.r.t. the $j$-agreement test.
--
--   This supplies assumption 4 of Theorem 4.1 (with $\alpha=\tau/4005$) in the proof of the goal theorem.
--
--   Differences from the source:
--   - generalization: Claim 5.8 under §5's standing assumption j ∣ r → no divisibility assumption; reason: Theorem 5.7 is stated for every r and needs the claim for every r; Appendix C (pp.83–84) extends the argument to j ∤ r; with j ∣ r it is the printed claim
--   - reading: 'With the parameters above' → the hypotheses of Theorem 5.7 on ε, r, p, d, X = X(p, r, m), and §5.2's j and τ; reason: the claim sits in §5.2, whose setting is that of Theorem 5.7, and is used only in Theorem 5.7's proof
--   - reading: the irreducible polynomial ϕ (choice suppressed, p.23) → every irreducible ϕ ∈ 𝔽_p[t] of degree m with ϕ(0) ≠ 0; reason: the paper suppresses the choice; the universal reading is the stronger one
--   - encoding: ε < 1/2 (with ε^{−1095}, log(1/ε) in the hypotheses) → 0 < ε < 1/2; reason: the hypotheses involve ε^{−1095} and log(1/ε), so ε > 0 is implicit
--   - encoding: the KMS complex and code → kmsComplex (top faces Γ = SL_r(𝔽_p[t]/(ϕ)), uniform μ) and kmsLineCodes (degree-≤ d polynomials under an affine parametrization of each co-rank-one star); reason: Definitions 2.35–2.36, 3.1 and footnote 9
--   - reading: log (base not stated) → Real.log (natural logarithm); reason: the paper does not fix the base; ln is the analyst's default and, as a lower-bound hypothesis, weaker than log₂ (ln x < log₂ x for x > 1)
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Claim 5.8, p.47 (PDF p.50); setting §5.2, p.46 (PDF p.49); Appendix C, pp.83–84 (PDF pp.86–87)

import Definitions.Def_LowAccLTC_kmsCode
import Definitions.Def_LowAccLTC_kmsParams
import Definitions.Def_LowAccLTC_IsJAgreementTestable

namespace LowAccLTC

/-- **Claim 5.8** (Ben Yaacov–Dikstein–Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs* (manuscript, sha256 04242e17…), p.47 = PDF p.50).

With the parameters of §5.2 (the hypotheses of Theorem 5.7, `j = ⌈10^15 ε^{-6} log(1/ε)⌉`,
`τ = 1/(10^23 (2j)^7 + 10)`), the KMS code `C(p, r, d, m)` is `(τ, x ↦ 801x/τ)`-agreement
testable w.r.t. the `j`-test.

**Formalization Note.** No divisibility `j ∣ r` is assumed (Appendix C, pp.83–84). -/
theorem claim_5_8_kms_agreement (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 2) (p r m d : ℕ) [Fact p.Prime]
    (hr : (10 : ℝ) ^ 2765 * ε ^ (-1095 : ℤ) * (Real.log (1 / ε)) ^ 182 ≤ r)
    (hp : (10 : ℝ) ^ 485 * (r : ℝ) ^ 6 * ε ^ (-156 : ℤ) * (Real.log (1 / ε)) ^ 26 ≤ p)
    (hd : (d : ℝ) ≤ p * ε ^ 2 / (1000 * r))
    (ϕ : Polynomial (ZMod p)) (hϕ : Irreducible ϕ) (hdeg : ϕ.natDegree = m) (h0 : ϕ.eval 0 ≠ 0)
    [Fintype (AdjoinRoot ϕ)] [DecidableEq (AdjoinRoot ϕ)] :
    (kmsComplex r ϕ).IsJAgreementTestable (kmsLineCodes r ϕ d) (kmsJ ε) (kmsTau ε)
      (fun x => 801 * x / kmsTau ε) := by sorry

end LowAccLTC
