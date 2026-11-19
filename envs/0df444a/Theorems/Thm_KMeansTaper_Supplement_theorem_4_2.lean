-- Prove2me | Theorems.Thm_KMeansTaper_Supplement_theorem_4_2
-- name    : KMeansTaper.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-18T06:30:26.462812+00:00
-- url     : https://prove2.me/theorems/1259742e-476e-496e-be74-439ee302f2ba
-- title:
--   Theorem 4.2 — the complete SFI taper window
-- statement:
--   Define
--
--   $$
--   c^\star=\frac{2}{3(e-2)}=0.92814\ldots.
--   $$
--
--   Then $\mathrm{SFI}(8,c)$ is false for every $c>c^\star$. In particular it is false for every $c\ge0.9282$ and for the original taper $c=1$. Together with Proposition 4.1(ii), it is false for every $c<3-\sqrt5$. By Theorem 3.2 it holds at the exact IEEE-double taper $c=c_{0.85}$.
--
--   This theorem bounds the parameter window of the SFI potential-function technique; it is not a hardness result for the rounding algorithm at $c=1$.
--
--   **Formalization Note** The decimal $0.9282$ is represented exactly as $4641/5000$. The constant $c_{0.85}$ is the published rational $7656119366529843/2^{53}$, not $17/20$. No upper bound $c\le1$ is imposed on the universal upper-failure statement.
--
--   Differences from the source:
--   - encoding: decimal $0.9282$ and the IEEE-double $c_{0.85}$ → the exact rationals $4641/5000$ and $7656119366529843/2^{53}$; reason: exact arithmetic represents the printed constants without rounding ambiguity
--   - encoding: "$\mathrm{SFI}(8,c)$ is false" → $\neg\mathrm{SFI}(8,c)$; reason: this is the direct propositional encoding of failure
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Theorem 4.2, p.7 (PDF p.10), proof in Appendix H.1, p.49 (PDF p.52)

import Mathlib
import Definitions.Def_KMeansTaper_SFI
import Definitions.Def_KMeansTaper_c085

namespace KMeansTaper
namespace Supplement

/-- **Theorem 4.2 (taper window)**, p.7 (PDF p.10).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3).

Writing `c⋆ = 2/(3(e-2))`, `SFI(8,c)` fails for every `c > c⋆`; in particular it fails
for every `c ≥ 0.9282` and at the original taper `c = 1`. Together with Proposition 4.1(ii),
it fails below `3 - √5`, while Theorem 3.2 gives the positive point `c = c₀.₈₅`.

**Formalization Note.** `0.9282` is the exact decimal rational `4641/5000`, and `c085` is the
published IEEE-double rational, not `17/20`. No assumption `c ≤ 1` is added to the upper failure
range. -/
theorem theorem_4_2 :
    let cstar : ℝ := 2 / (3 * (Real.exp 1 - 2))
    (∀ c : ℝ, cstar < c → ¬ SFI 8 c) ∧
    (∀ c : ℝ, (4641 : ℝ) / 5000 ≤ c → ¬ SFI 8 c) ∧
    ¬ SFI 8 1 ∧
    (∀ c : ℝ, c < 3 - Real.sqrt 5 → ¬ SFI 8 c) ∧
    SFI 8 (c085 : ℝ) := by sorry

end Supplement
end KMeansTaper
