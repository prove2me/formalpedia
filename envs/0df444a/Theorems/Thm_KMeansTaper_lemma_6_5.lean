-- Prove2me | Theorems.Thm_KMeansTaper_lemma_6_5
-- name    : KMeansTaper.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:07:01.60421+00:00
-- url     : https://prove2.me/theorems/aeaa3c9d-4583-48e9-9bf4-3b89123e1e0c
-- title:
--   Lemma 6.5 — local lemma at the tight point
-- statement:
--   Let $\kappa=8$, $c=c_{0.85}$, $(\alpha_z,\gamma_z)=(2,6)$, $s=0$, $\alpha=0$, $\beta(D)=D-1$, transfer thresholds $(3/8,9/16,2)$, and let $N$, $\Phi$, $S$, $S_0$, $G_1$, $S_{qq}$ be as in the definition `phiLoc`. Write $u=\delta-1$, $v=\zeta-1$, $D=\delta^2$, $P=P(x)$, $m=m(8,x)$. Then on $N$:
--
--   1. $\Phi\le0$, and $\Phi=0$ exactly at $w=q=0$, $\delta=\zeta=1$;
--   2. $\Phi\le S$, and $S=S_0+qG_1+\frac{q^2}{2}S_{qq}(\xi)$ for some $0\le\xi\le q$;
--   3. (a) $S_0=-2u^2-2v^2-2uv(u+v)-u^2v^2-(2D+6)Pw^2\le-\frac{15}{8}(u^2+v^2)-2w^2$;
--   4. (c) $|\partial_wG_1|\le9$, $|\partial_\delta G_1|\le6$, $|\partial_\zeta G_1|\le5$ and $S_{qq}\le0$;
--
--   and (b) for all $x\in[0,1]$, $g_q(x):=G_1(w=0,u=v=0)=12cP+16Px+m-8\le-\frac{6}{25}$.
--
--   The lemma closes the neighbourhood of the uniform configuration, where (13) is tight and no interval bound can be negative.
--
--   **Formalization Note** Partial derivatives are derivatives of the one-variable sections of $G_1$ at the point.
--
--   Differences from the source:
--   - reading: Φ ≤ 0 on N, with equality only at w = q = 0, δ = ζ = 1 → Φ ≤ 0 on N and Φ = 0 ↔ (w = 0 ∧ q = 0 ∧ δ = 1 ∧ ζ = 1) on N; reason: the stronger reading: equality holds at that point (Φ = 0 there since a ≥ 1) and only there
--   - encoding: ∂_w G1, ∂_δ G1, ∂_ζ G1, S_qq(ξ) → deriv of the one-variable sections; Sqq the second deriv in q; reason: G1 and S are smooth near N (1 − cPq ≥ 1/2)
--   - encoding: Φ in the variables (x, ω, δ, q, ζ) with w = (1 − x)ω → phiLoc in (x, w, δ, q, ζ); reason: N is stated in w
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Lemma 6.5, p.16 (PDF p.19), with Φ of Section 6.1, p.13 (PDF p.16)

import Mathlib
import Definitions.Def_KMeansTaper_coefP
import Definitions.Def_KMeansTaper_c085
import Definitions.Def_KMeansTaper_phiLoc

namespace KMeansTaper

/-- **Lemma 6.5 (local lemma at the tight point)**, p.16 (PDF p.19), with `Φ` of Section 6.1,
p.13 (PDF p.16).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3).

Let `κ = 8`, `c = c_{0.85}`, `(α_z, γ_z) = (2, 6)`, `s = 0`, `α = 0`, `β(D) = D - 1` and `N`
the region `NLoc`. Then `Φ ≤ 0` on `N`, with equality only at `w = q = 0`, `δ = ζ = 1`. More
precisely `Φ ≤ S` on `N` and, with `u = δ - 1`, `v = ζ - 1`, `S = S₀ + q G₁ + (q²/2) S_qq(ξ)`
(`0 ≤ ξ ≤ q`), where
(a) `S₀ = -2u² - 2v² - 2uv(u + v) - u²v² - (2D + 6)Pw² ≤ -(15/8)(u² + v²) - 2w²`;
(b) `g_q(x) := G₁(w = 0, u = v = 0) = 12cP + 16Px + m - 8 ≤ -6/25` for all `x ∈ [0, 1]`;
(c) `|∂_w G₁| ≤ 9`, `|∂_δ G₁| ≤ 6`, `|∂_ζ G₁| ≤ 5` and `S_qq ≤ 0` on `N`.

**Formalization Note.** The thresholds of `Φ` are those of (K1), `(3/8, 9/16, 2)`. "Equality
only at" is stated as an equivalence on `N`. The partial derivatives are `deriv` of the
one-variable sections of `G₁`; `P`, `m = m(8, ·)` are evaluated at `x`. -/
theorem lemma_6_5 :
    (∀ x w δ q ζ : ℝ, NLoc x w δ q ζ → phiLoc x w δ q ζ ≤ 0) ∧
    (∀ x w δ q ζ : ℝ, NLoc x w δ q ζ →
      (phiLoc x w δ q ζ = 0 ↔ w = 0 ∧ q = 0 ∧ δ = 1 ∧ ζ = 1)) ∧
    (∀ x w δ q ζ : ℝ, NLoc x w δ q ζ → phiLoc x w δ q ζ ≤ Sloc x w δ q ζ) ∧
    (∀ x w δ q ζ : ℝ, NLoc x w δ q ζ → ∃ ξ ∈ Set.Icc (0 : ℝ) q,
      Sloc x w δ q ζ = S0 x w δ ζ + q * G1 x w δ ζ + q ^ 2 / 2 * Sqq x w δ ξ ζ) ∧
    (∀ x w δ q ζ : ℝ, NLoc x w δ q ζ →
      S0 x w δ ζ = -2 * (δ - 1) ^ 2 - 2 * (ζ - 1) ^ 2 - 2 * (δ - 1) * (ζ - 1) * ((δ - 1) + (ζ - 1))
          - (δ - 1) ^ 2 * (ζ - 1) ^ 2 - (2 * δ ^ 2 + 6) * coefP x * w ^ 2 ∧
        S0 x w δ ζ ≤ -(15 / 8) * ((δ - 1) ^ 2 + (ζ - 1) ^ 2) - 2 * w ^ 2) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      G1 x 0 1 1 = 12 * (c085 : ℝ) * coefP x + 16 * coefP x * x + coefM 8 x - 8 ∧
        G1 x 0 1 1 ≤ -(6 / 25)) ∧
    (∀ x w δ q ζ : ℝ, NLoc x w δ q ζ →
      |deriv (fun w' => G1 x w' δ ζ) w| ≤ 9 ∧ |deriv (fun δ' => G1 x w δ' ζ) δ| ≤ 6 ∧
        |deriv (fun ζ' => G1 x w δ ζ') ζ| ≤ 5 ∧ Sqq x w δ q ζ ≤ 0) := by sorry

end KMeansTaper
