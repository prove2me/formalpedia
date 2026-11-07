-- Prove2me | Theorems.Thm_MFHeisGibbs_corollary_6
-- name    : MFHeisGibbs.corollary_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:25.68846+00:00
-- url     : https://prove2.me/theorems/cffa339d-8164-4193-8f36-2de5d143a071
-- title:
--   Corollary 6, (130)–(132) — OFT gap lower bounds on $R_n^\perp$, $P_n^\perp$, $P_n$, $R_n$
-- statement:
--   Let $0<\beta<\infty$, $\sigma>0$, $f$ satisfy (4) and $n\ge2$, and let $\Phi$ be the standard normal distribution function. Then
--
--   $$\gamma(\mathcal L_{F,\sigma},R_n^\perp)\ge\frac{4c_\star}{n}\Big[1-\Phi\Big(\max\Big\{\frac\sigma2,\frac\beta{2\sigma}\Big\}\Big)\Big],$$
--
--   $$\gamma(\mathcal L_{F,\sigma},P_n^\perp)\ge\frac{c_\star\beta}{54\,\sigma\sqrt{2\pi}}\exp\Big(-\beta-\frac{2\beta^2}{\sigma^2}-\frac{(\beta+\sigma^2/2)^2}{2\sigma^2}\Big),$$
--
--   $$\gamma(\mathcal L_{F,\sigma},V)\ge c_\star\Big[1-\Phi\Big(\max\Big\{\frac\sigma2,\frac\beta{2\sigma}\Big\}\Big)\Big]\gamma(\mathcal L_C,V)\qquad(V\in\{P_n,R_n\}).$$
--
--   These transfer every lower bound from the coherent generator to the OFT generator.
--
--   Differences from the source:
--   - encoding: the Dirichlet form and the KMS norm, which are real for these generators → the real part of the complex inner product; reason: Lean's kmsInner is complex-valued
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), Corollary 6, (130)–(132), pp.54–55 (PDF 55–56)

import Definitions.Def_MFHeisGibbs_Generators
import Definitions.Def_MFHeisGibbs_KMS

namespace MFHeisGibbs

/-- **Corollary 6 (OFT gap lower bounds)**, (130)–(132), Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…),
pp.54–55. For `0 < β < ∞`, `σ > 0`, `f` with (4), `n ≥ 2`.

**Formalization Note.** The sector gaps are the Rayleigh infima of (27) restricted to the sector, as the
page says on p.51, (120). -/
theorem corollary_6 (f : ℝ → ℂ) (hf : IsKMSFilter f) (β : ℝ) (hβ : 0 < β) (s : ℝ) (hs : 0 < s)
    (n : ℕ) (hn : 2 ≤ n) :
    (4 * cStar f / (n : ℝ)) * (1 - normalCdf (max (s / 2) (β / (2 * s)))) ≤
      sectorGap β (LF β s f n) (hsPerp (Rn n)) ∧
    (cStar f * β / (54 * s * Real.sqrt (2 * Real.pi))) *
        Real.exp (-β - 2 * β ^ 2 / s ^ 2 - (β + s ^ 2 / 2) ^ 2 / (2 * s ^ 2)) ≤
      sectorGap β (LF β s f n) (hsPerp (Pn n)) ∧
    (∀ V ∈ ({Pn n, Rn n} : Set (Set (Op n))),
      cStar f * (1 - normalCdf (max (s / 2) (β / (2 * s)))) * sectorGap β (LC β f n) V ≤
        sectorGap β (LF β s f n) V) := by sorry

end MFHeisGibbs
