-- Prove2me | Theorems.Thm_LowAccLTC_theorem_5_7_kms_low_acceptance
-- name    : LowAccLTC.theorem_5_7_kms_low_acceptance
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:39:53.884326+00:00
-- url     : https://prove2.me/theorems/82fbf0a8-4428-45dd-8987-7996e83e81a0
-- title:
--   Theorem 5.7 — KMS codes over $\mathbb F_p$ are $(\varepsilon,x\mapsto x/4)$-LA LTCs under the vertex test
-- statement:
--   Let $0<\varepsilon<\frac12$, let $r,m,d\in\mathbb N$ and let $p$ be prime, with
--   $$r\ \ge\ 10^{2765}\varepsilon^{-1095}\log^{182}\frac1\varepsilon,\qquad p\ \ge\ 10^{485}r^6\varepsilon^{-156}\log^{26}\frac1\varepsilon,\qquad d\ \le\ \frac{p\varepsilon^2}{1000r}.$$
--   Let $\phi\in\mathbb F_p[t]$ be irreducible of degree $m$ with $\phi(0)\neq0$, $X=X(p,r,m)$ the KMS complex and $C=C(p,r,d,m)$ the KMS code. Then:
--   1. $C$ is an $(\varepsilon,\ x\mapsto x/4)$-LA LTC w.r.t. the vertex test: for every word $f:\Gamma\to\mathbb F_p$, if $x:=1-\mathbb E_{v}[\mathrm{dist}(f|_v,C_v)]\ge\varepsilon$ then $1-\mathrm{dist}(f,C)\ge x/4$;
--   2. every vertex star has exactly $p^{\binom r2}$ top faces (the query complexity of the vertex test);
--   3. $\#X\langle1\rangle\cdot p^{\binom r2}=r\,|\Gamma|$ (so the test uses $\log_2\#X\langle1\rangle=\log N-\log(p^{\binom r2}/r)$ random bits, $N=|\Gamma|$).
--
--   In the regime $p,r=\mathrm{poly}(1/\varepsilon)$ of Theorem 1.1 this is a low-acceptance local test with $\exp(\mathrm{poly}(1/\varepsilon))$ queries and $\log N-\mathrm{poly}(1/\varepsilon)$ random bits, independent of $m$.
--
--   Differences from the source:
--   - generalization: the conclusion '(ε, x ↦ x/4)-LA LTC w.r.t. the vertex test' → that conclusion together with the exact counts star(v) = p^(r choose 2) and #vertices · p^(r choose 2) = r·|Γ|; reason: the counts are the query and randomness content of the informal Theorem 1.1 (p.4); dropping them gives the printed theorem
--   - reading: the irreducible polynomial ϕ (choice suppressed, p.23) → every irreducible ϕ ∈ 𝔽_p[t] of degree m with ϕ(0) ≠ 0; reason: the paper suppresses the choice; the universal reading is the stronger one
--   - encoding: ε < 1/2 (with ε^{−1095}, log(1/ε) in the hypotheses) → 0 < ε < 1/2; reason: the hypotheses involve ε^{−1095} and log(1/ε), so ε > 0 is implicit
--   - encoding: the KMS complex and code → kmsComplex (top faces Γ = SL_r(𝔽_p[t]/(ϕ)), uniform μ) and kmsLineCodes (degree-≤ d polynomials under an affine parametrization of each co-rank-one star); reason: Definitions 2.35–2.36, 3.1 and footnote 9
--   - reading: log (base not stated) → Real.log (natural logarithm); reason: the paper does not fix the base; ln is the analyst's default and, as a lower-bound hypothesis, weaker than log₂ (ln x < log₂ x for x > 1)
--   - encoding: (ε, φ)-LA LTC with φ : [0,1] → ℝ₊ monotone, ε ∈ (0,1) → IsLALTCVertex: the bare implication x ≥ ε ⇒ 1 − dist(f, C) ≥ φ(x); reason: the side conditions on φ and ε are hypotheses where the paper assumes them; bundling them would make a conclusion with a possibly negative φ false although the paper's claim is the implication
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Theorem 5.7, p.46 (PDF p.49); Theorem 1.1, p.4 (PDF p.7)

import Definitions.Def_LowAccLTC_kmsCode
import Definitions.Def_LowAccLTC_IsLALTCVertex

namespace LowAccLTC

/-- **Theorem 5.7** (Ben Yaacov–Dikstein–Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs* (manuscript, sha256 04242e17…), p.46 = PDF p.49), with the query and randomness counts of its
informal version Theorem 1.1 (p.4).

Let `0 < ε < 1/2`, `r, m, d ∈ ℕ`, `p` prime, with `r ≥ 10^2765 ε^-1095 log^182(1/ε)`,
`p ≥ 10^485 r^6 ε^-156 log^26(1/ε)` and `d ≤ pε²/(1000r)`. For every irreducible
`ϕ ∈ 𝔽_p[t]` of degree `m` with `ϕ(0) ≠ 0`, the KMS code `C(p, r, d, m)` is an
`(ε, x ↦ x/4)`-LA LTC w.r.t. the vertex test; moreover every vertex star has `p^(r choose 2)` top
faces and `#vertices · p^(r choose 2) = r · |Γ|`.

**Formalization Note.** `log` is the natural logarithm; colours are `Fin r`; the top faces are
`Γ = SL_r(𝔽_p[t]/(ϕ))` with the uniform measure; lines are identified with `𝔽_p` by affine
parametrizations (footnote 9); `ε > 0` is explicit. -/
theorem theorem_5_7_kms_low_acceptance (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 2) (p r m d : ℕ) [Fact p.Prime]
    (hr : (10 : ℝ) ^ 2765 * ε ^ (-1095 : ℤ) * (Real.log (1 / ε)) ^ 182 ≤ r)
    (hp : (10 : ℝ) ^ 485 * (r : ℝ) ^ 6 * ε ^ (-156 : ℤ) * (Real.log (1 / ε)) ^ 26 ≤ p)
    (hd : (d : ℝ) ≤ p * ε ^ 2 / (1000 * r))
    (ϕ : Polynomial (ZMod p)) (hϕ : Irreducible ϕ) (hdeg : ϕ.natDegree = m) (h0 : ϕ.eval 0 ≠ 0)
    [Fintype (AdjoinRoot ϕ)] [DecidableEq (AdjoinRoot ϕ)] :
    (kmsComplex r ϕ).IsLALTCVertex (kmsLineCodes r ϕ d) ε (fun x => x / 4) ∧
    (∀ (g : KMSGamma r ϕ) (i : Fin r),
      ((kmsComplex r ϕ).star {(kmsComplex r ϕ).vert g i}).card = p ^ r.choose 2) ∧
    (kmsComplex r ϕ).vertices.card * p ^ r.choose 2 = r * Fintype.card (KMSGamma r ϕ) := by sorry

end LowAccLTC
