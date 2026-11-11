-- Prove2me | Theorems.Thm_HZFixp_Main_lemma_3_8
-- name    : HZFixp.Main.lemma_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:53:33.721+00:00
-- url     : https://prove2.me/theorems/5c35c328-358e-4713-9dcf-9f0a4ca8ee3c
-- title:
--   Lemma 3.8 — with the center (11), a reciprocal gate's input contribution is at most ε|h|
-- statement:
--   Let a reciprocal gate have $\kappa>0$, $c\ge0$, input interval $[a,b]$ with $a>0$, output interval $[\ell,u]\subset(0,\infty)$ containing $[J(b),J(a)]$, and let $\varepsilon>0$. With the center
--   $$T=\Big\lceil \max\Big\{1,\ 20(u+|\beta|),\ \frac{128\kappa(\kappa+c)}{(a+c)^2\varepsilon}\Big\}\Big\rceil \tag{11}$$
--   the input contribution $P_A$ and the output contribution $h$ of (9) satisfy
--   $$|P_A| \le \varepsilon\,|h| \qquad\text{for all } x\in[\ell,u],\ y\in[0.999T,1.001T],\ A\in[a,b].$$
--
--   Making the centre large makes a gate's effect on its input negligible relative to its output contribution, which is what lets gadgets be connected without destroying exactness.
--
--   Differences from the source:
--   - generalization: rational κ, c, β, endpoints and ε → real parameters; reason: pointwise real analysis; rational values are a special case
--   - reading: reciprocal gate J(A) = κ/(A + c) + β (§3.3.2, Figure 6) → κ > 0 and c ≥ 0; reason: κ/R_T² and κ/(R_T D_T) are edge multiplicities and D_T/R_T an edge ratio, so κ > 0 and D_T = κ + R_T c > 0 for every admissible center T, which for arbitrarily large T (11) means c ≥ 0; every reciprocal gate of §3.3.1 has c ∈ {0, 1}
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), p. 19 (PDF 21), Lemma 3.8; (11) p. 17 (PDF 19); proof p. 51 (PDF 53)

import Mathlib
import Definitions.Def_HZFixp_Main_Gates

namespace HZFixp.Main

/-- **Lemma 3.8.** For the center chosen in (11), the reciprocal gate satisfies `|P_A| ≤ ε|h|`
throughout its box. -/
theorem lemma_3_8 (κ c β a b ℓ u ε T : ℝ) (hκ : 0 < κ) (hc : 0 ≤ c) (ha : 0 < a) (hab : a ≤ b)
    (hℓ : 0 < ℓ) (hℓJ : ℓ ≤ recJ κ c β b) (hJu : recJ κ c β a ≤ u) (hε : 0 < ε)
    (hT : T = (recCenter κ c β a u ε : ℝ)) :
    ∀ x ∈ Set.Icc ℓ u, ∀ y ∈ Set.Icc (0.999 * T) (1.001 * T), ∀ A ∈ Set.Icc a b,
      |recP κ c β T y A| ≤ ε * |gateH 1 x y T| := by sorry

end HZFixp.Main
