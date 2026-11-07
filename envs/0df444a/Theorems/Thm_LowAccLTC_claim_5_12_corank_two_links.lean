-- Prove2me | Theorems.Thm_LowAccLTC_claim_5_12_corank_two_links
-- name    : LowAccLTC.claim_5_12_corank_two_links
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:40:54.300175+00:00
-- url     : https://prove2.me/theorems/4e08d045-5aca-4fea-940f-118092b00b84
-- title:
--   Claim 5.12 — on good $Y^{\mathcal P}$, co-rank-two link codes are $(3\tau,\ x\mapsto x/(5\tau))$-agreement testable
-- statement:
--   In the setting of §5.2 — $0<\varepsilon<1/2$, $p$ prime, $r,m,d\in\mathbb N$ with $r\ge10^{2765}\varepsilon^{-1095}\log^{182}(1/\varepsilon)$, $p\ge10^{485}r^6\varepsilon^{-156}\log^{26}(1/\varepsilon)$ and $d\le p\varepsilon^2/(1000r)$, $X=X(p,r,m)$ for an irreducible $\phi\in\mathbb F_p[t]$ of degree $m$ with $\phi(0)\ne0$, $C=C(p,r,d,m)$, $j=\lceil10^{15}\varepsilon^{-6}\log(1/\varepsilon)\rceil$ and $\tau=1/(10^{23}(2j)^7+10)$, and $j\mid r$, $k=r/j$ — let $\mathcal P:[r]\to[k]$ be a good even partition and $t$ a face of $Y^{\mathcal P}$ of co-rank two. Then the local code $C_t$ on the link $Y^{\mathcal P}_t$ is
--   $$\Big(3\tau,\ x\mapsto\frac{x}{5\tau}\Big)\text{-agreement testable}$$
--   w.r.t. the vertex agreement test on $Y^{\mathcal P}_t$: its link vertices are the $j$-faces $s$ coloured by the two blocks missing from $t$, with local codes $C_{t\cup s}$.
--
--   This is the base case of the trickling-down induction in the proof of Claim 5.8.
--
--   Differences from the source:
--   - reading: the setting of §5.2 (Claim 5.12 states no parameters) → the hypotheses of Theorem 5.7 on ε, r, p, d, X = X(p, r, m), §5.2's j and τ, and §5's standing j ∣ r; reason: the claim sits in §5.2, whose setting is that of Theorem 5.7, and is used only in Claim 5.8's proof
--   - reading: the irreducible polynomial ϕ (choice suppressed, p.23) → every irreducible ϕ ∈ 𝔽_p[t] of degree m with ϕ(0) ≠ 0; reason: the paper suppresses the choice; the universal reading is the stronger one
--   - encoding: ε < 1/2 (with ε^{−1095}, log(1/ε) in the hypotheses) → 0 < ε < 1/2; reason: the hypotheses involve ε^{−1095} and log(1/ε), so ε > 0 is implicit
--   - encoding: the KMS complex and code → kmsComplex (top faces Γ = SL_r(𝔽_p[t]/(ϕ)), uniform μ) and kmsLineCodes (degree-≤ d polynomials under an affine parametrization of each co-rank-one star); reason: Definitions 2.35–2.36, 3.1 and footnote 9
--   - reading: log (base not stated) → Real.log (natural logarithm); reason: the paper does not fix the base; ln is the analyst's default and, as a lower-bound hypothesis, weaker than log₂ (ln x < log₂ x for x > 1)
--   - encoding: the code C_t on Y^P_t w.r.t. the vertex agreement test → IsVATestable on colorRestrict X P at the face t, with local codes C_{⋃t ∪ s} of X and target C_{⋃t}; reason: Definition 5.10 on the link: the local code of a link vertex s is the code on star(t ∪ s)
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Claim 5.12, p.48 (PDF p.51); setting §5.2, p.46 (PDF p.49); §5 standing j ∣ r, p.42

import Definitions.Def_LowAccLTC_kmsCode
import Definitions.Def_LowAccLTC_kmsParams
import Definitions.Def_LowAccLTC_colorRestrict
import Definitions.Def_LowAccLTC_IsVATestable
open scoped Classical

namespace LowAccLTC

/-- **Claim 5.12** (Ben Yaacov–Dikstein–Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs* (manuscript, sha256 04242e17…), p.48 = PDF p.51).

In the setting of §5.2 (the hypotheses of Theorem 5.7, `X = X(p, r, m)`, `C` the KMS code,
`j = ⌈10^15 ε^{-6} log(1/ε)⌉`, `τ = 1/(10^23 (2j)^7 + 10)`, `k = r/j`, `j ∣ r`): for every good
even partition `P` and every face `t ∈ Y^P` of co-rank two, the code `C_t` on the link `Y^P_t` is
`(3τ, x ↦ x/(5τ))`-agreement testable w.r.t. the vertex agreement test. -/
theorem claim_5_12_corank_two_links (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 2) (p r m d : ℕ) [Fact p.Prime]
    (hr : (10 : ℝ) ^ 2765 * ε ^ (-1095 : ℤ) * (Real.log (1 / ε)) ^ 182 ≤ r)
    (hp : (10 : ℝ) ^ 485 * (r : ℝ) ^ 6 * ε ^ (-156 : ℤ) * (Real.log (1 / ε)) ^ 26 ≤ p)
    (hd : (d : ℝ) ≤ p * ε ^ 2 / (1000 * r))
    (ϕ : Polynomial (ZMod p)) (hϕ : Irreducible ϕ) (hdeg : ϕ.natDegree = m) (h0 : ϕ.eval 0 ≠ 0)
    [Fintype (AdjoinRoot ϕ)] [DecidableEq (AdjoinRoot ϕ)]
    (hdvd : kmsJ ε ∣ r) (P : Fin r → Fin (r / kmsJ ε)) (hPeven : IsEvenPartition (kmsJ ε) P)
    (hPgood : IsGoodPartition P)
    (tY : Finset (Fin (r / kmsJ ε) × Finset (Fin r × Set (KMSGamma r ϕ))))
    (htY : ((kmsComplex r ϕ).colorRestrict P).IsFace tY) (hco : tY.card + 2 = r / kmsJ ε) :
    ((kmsComplex r ϕ).colorRestrict P).IsVATestable tY
      (fun w => (kmsComplex r ϕ).localCode (kmsLineCodes r ϕ d)
        (PartiteComplex.unionFace tY ∪ w.2))
      ((kmsComplex r ϕ).localCode (kmsLineCodes r ϕ d) (PartiteComplex.unionFace tY))
      (3 * kmsTau ε) (fun x => x / (5 * kmsTau ε)) := by sorry

end LowAccLTC
