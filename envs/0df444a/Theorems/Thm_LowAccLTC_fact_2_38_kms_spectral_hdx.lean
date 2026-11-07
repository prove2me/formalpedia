-- Prove2me | Theorems.Thm_LowAccLTC_fact_2_38_kms_spectral_hdx
-- name    : LowAccLTC.fact_2_38_kms_spectral_hdx
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:30.223423+00:00
-- url     : https://prove2.me/theorems/c70fe109-48b9-4841-b275-00ab0a54499a
-- title:
--   Fact 2.38 [GV25] — KMS complexes are $\frac{1}{\sqrt q-(r-2)}$-one-sided spectral HDXs with vertex degree $q^{\binom r2}$
-- statement:
--   Let $\mathbb F_q$ be a finite field, $r\ge3$, $m\ge1$, and $\phi\in\mathbb F_q[t]$ irreducible of degree $m$ with $\phi(0)\neq0$. If $q\ge(r-1)^2$, then the KMS complex $X(q,r,m)$ is a
--   $$\frac{1}{\sqrt q-(r-2)}\text{-one-sided spectral HDX},$$
--   and every vertex belongs to exactly $q^{\binom r2}$ top faces.
--
--   In the proof of the goal theorem this gives assumption 1 of Theorem 4.1 (with $q=p\ge4(r-1)^2$ the bound is at most $4/\sqrt p\le r^{-2}$), and the vertex count gives the query complexity of the vertex test.
--
--   Differences from the source:
--   - encoding: q a prime power, F_q → a finite field F with q = Fintype.card F; reason: every finite field has prime-power order and every prime power is the order of a finite field
--   - reading: 'Thus, for fixed q, r, these complexes have bounded degree as m grows' → not a separate clause; reason: it is a consequence of the exact count q^(r choose 2), which does not depend on m
--   - encoding: λ₂ of the link graph's random-walk operator is at most λ → the variational form E_{(u,v)} g(u)g(v) ≤ λ E g² for every g of mean 0 under the link's vertex law; reason: equivalent by self-adjointness and Courant–Fischer
--   - encoding: the coset complex CC(Γ; H₁,…,H_r) with vertices gH_i → kmsComplex: top faces Γ, the vertex of colour i of g is the pair (i, gH_i); reason: top faces are in bijection with Γ because ⋂ H_i = {1} (p.22)
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Fact 2.38 ([GV25, Theorem 4.3]), p.23 (PDF p.26)

import Definitions.Def_LowAccLTC_kmsComplex
import Definitions.Def_LowAccLTC_IsOneSidedLocalSpectral

namespace LowAccLTC

/-- **Fact 2.38** ([GV25, Theorem 4.3]; Ben Yaacov–Dikstein–Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs* (manuscript, sha256 04242e17…), p.23 = PDF p.26).

Let `F` be a finite field with `q` elements, `r ≥ 3`, `m ≥ 1`, and `ϕ ∈ F[t]` irreducible of
degree `m` with `ϕ(0) ≠ 0`. If `q ≥ (r - 1)²`, the KMS complex `X(q, r, m)` is a
`1/(√q - (r - 2))`-one-sided spectral HDX, and every vertex belongs to exactly `q^(r choose 2)`
top faces. -/
theorem fact_2_38_kms_spectral_hdx {F : Type*} [Field F] [Fintype F] (r m : ℕ) (hr : 3 ≤ r)
    (hm : 1 ≤ m) (ϕ : Polynomial F) (hϕ : Irreducible ϕ) (hdeg : ϕ.natDegree = m)
    (h0 : ϕ.eval 0 ≠ 0) [Fintype (AdjoinRoot ϕ)] [DecidableEq (AdjoinRoot ϕ)]
    (hq : (r - 1) ^ 2 ≤ Fintype.card F) :
    (kmsComplex r ϕ).IsOneSidedLocalSpectral
        (1 / (Real.sqrt (Fintype.card F) - ((r : ℝ) - 2))) ∧
    ∀ (g : KMSGamma r ϕ) (i : Fin r),
      ((kmsComplex r ϕ).star {(kmsComplex r ϕ).vert g i}).card = Fintype.card F ^ r.choose 2 := by sorry

end LowAccLTC
