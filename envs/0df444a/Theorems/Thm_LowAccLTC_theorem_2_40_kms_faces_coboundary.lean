-- Prove2me | Theorems.Thm_LowAccLTC_theorem_2_40_kms_faces_coboundary
-- name    : LowAccLTC.theorem_2_40_kms_faces_coboundary
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:40:21.967297+00:00
-- url     : https://prove2.me/theorems/83c61491-2291-4ded-84db-df274b30f707
-- title:
--   Theorem 2.40 [DOB26] — $\mathcal F^jX$ of a KMS complex over $\mathbb F_p$ is an $(m',1/j^{173})$-coboundary expander for $j\le r^{0.1}$
-- statement:
--   Let $X=X(p,r,m)$ be a KMS complex of rank $r\ge3$ over the prime field $\mathbb F_p$ ($\phi\in\mathbb F_p[t]$ irreducible of degree $m\ge1$, $\phi(0)\ne0$). Then for every integer $1\le j\le r^{0.1}$ and every list size $1\le m'\le p$, the $j$-faces complex $\mathcal F^jX$ is an
--   $$\Big(m',\ \frac{1}{j^{173}}\Big)\text{-coboundary expander}.$$
--
--   This supplies assumption 2 of Theorem 4.1 for KMS codes, with $m'=\lceil6/\varepsilon\rceil\le p$.
--
--   Differences from the source:
--   - reading: for m = max(char(F_p), exp(Ω(√log p))) → for every list size 1 ≤ m' ≤ p; reason: the Ω has no stated constant, so the printed value is not a definite number; the proof of Theorem 5.7 (p.47) uses the theorem for M = ⌈6/ε⌉ ≤ p, and max(char 𝔽_p, ·) ≥ p = char 𝔽_p
--   - reading: 'a KMS complex of rank r over the field F_p' → X(p, r, m) for p prime, r ≥ 3, m ≥ 1 and every irreducible ϕ of degree m with ϕ(0) ≠ 0; reason: Definition 2.36's standing conditions; the paper suppresses the choice of ϕ (p.23), read universally
--   - encoding: Sym(m) and oriented faces of F^jX → Equiv.Perm (Fin m'), oriented edges/triangles as ordered disjoint j-colour-sets of a top face; reason: the induced laws of Definition 2.14
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Theorem 2.40 ([DOB26]), p.23 (PDF p.26)

import Definitions.Def_LowAccLTC_kmsComplex
import Definitions.Def_LowAccLTC_IsFacesCoboundaryExpander

namespace LowAccLTC

/-- **Theorem 2.40** ([DOB26]; Ben Yaacov–Dikstein–Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs* (manuscript, sha256 04242e17…), p.23 = PDF p.26).

Let `X` be a KMS complex of rank `r ≥ 3` over the prime field `𝔽_p` (with `ϕ ∈ 𝔽_p[t]`
irreducible of degree `m ≥ 1`, `ϕ(0) ≠ 0`). For every `1 ≤ j ≤ r^0.1`, the `j`-faces complex
`F^j X` is an `(m', 1/j^173)`-coboundary expander for every list size `1 ≤ m' ≤ p`.

**Formalization Note.** The printed `m = max(char(𝔽_p), exp(Ω(√log p)))` has an unspecified
constant; it is read as "every `m' ≤ p = char 𝔽_p`", which is how the proof of Theorem 5.7 uses
it (p.47). -/
theorem theorem_2_40_kms_faces_coboundary (p r m : ℕ) [Fact p.Prime] (hr : 3 ≤ r) (hm : 1 ≤ m)
    (ϕ : Polynomial (ZMod p)) (hϕ : Irreducible ϕ) (hdeg : ϕ.natDegree = m) (h0 : ϕ.eval 0 ≠ 0)
    [Fintype (AdjoinRoot ϕ)] [DecidableEq (AdjoinRoot ϕ)]
    (j : ℕ) (hj : 1 ≤ j) (hjr : (j : ℝ) ≤ (r : ℝ) ^ (1 / 10 : ℝ))
    (m' : ℕ) (hm' : 1 ≤ m') (hm'p : m' ≤ p) :
    (kmsComplex r ϕ).IsFacesCoboundaryExpander j m' (1 / (j : ℝ) ^ 173) := by sorry

end LowAccLTC
