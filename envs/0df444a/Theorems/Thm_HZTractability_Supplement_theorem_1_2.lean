-- Prove2me | Theorems.Thm_HZTractability_Supplement_theorem_1_2
-- name    : HZTractability.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:30:33.226467+00:00
-- url     : https://prove2.me/theorems/a0363eff-ad0c-4fbc-8772-f973f9fa68e4
-- title:
--   Theorem 1.2 — constant-error hardness under PCP for PPAD
-- statement:
--   Assume the PCP-for-PPAD conjecture, in the form: for some rational $\delta\in(0,1]$, weak $\delta$-Pure-Circuit is PPAD-hard. Then for every rational $a$ with $0<a<1$ there is a rational constant $\varepsilon_0=\varepsilon_0(a)>0$ such that the following search problem is PPAD-hard:
--   $$\text{given } N\ge1 \text{ and } u\in\{0,a,1\}^{N\times N},\ \text{find a normalized additive } \varepsilon_0\text{-equilibrium of the HZ market } u.$$
--
--   The accuracy is a constant, independent of the market size, in contrast with the accuracy $\varepsilon^*(a)/N$ of Theorem 1.1. It rules out a PTAS for HZ equilibria with three utility values under the conjecture, unless PPAD $\subseteq$ P.
--
--   **Formalization Note** PPAD-hardness in the hypothesis and in the conclusion is the same published notion `CEPolytopeHard.PPADHard`. $\varepsilon_0$ is chosen after $a$ and before any instance.
--
--   Differences from the source:
--   - reading: Assuming the PCP-for-PPAD conjecture → hypothesis PCPforPPAD: weak δ-Pure-Circuit without the input-once restriction is PPAD-hard for some rational δ ∈ (0, 1]; reason: the paper fixes the conjecture through [DFHM26, Theorem 2.2] (p.20), listing the forms with and without the input-once restriction as equivalent; the unrestricted form is the weakest of them, so the theorem is the strongest; rational δ loses nothing since hardness is monotone in δ
--   - encoding: an HZ market with utilities in {0, a, 1} and its normalized additive ε0-equilibria → search problem HZConstError a ε₀: codes encRatMatrix N u (N ≥ 1, one common a) and answers encRatMatrix N x ++ encRatVec N p with rational x, p satisfying IsNormAddEq; reason: a concrete encoding of the search problem; rational answers exist (Lemma 4.11)
--   - encoding: PPAD-hard → CEPolytopeHard.PPADHard (every problem of QuasiStrictNE.PPAD reduces by CardinalMatching.SearchReduces); reason: the platform's published PPAD layer, the same one used by the base mission's Theorem 1.1
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Theorem 1.2, p.2 (PDF p.4); proof p.24 (PDF p.26)

import Mathlib
import Definitions.Def_CEPolytopeHard_PPADHard
import Definitions.Def_HZTractability_Supplement_PCPforPPAD
import Definitions.Def_HZTractability_Supplement_HZConstError

namespace HZTractability.Supplement

/-- **Theorem 1.2 (Constant-error hardness under PCP for PPAD)** (Panageas–Shein–Taherijam–Vazirani,
arXiv:2610.35848, held version, sha256 74b7bf9f…, p.2 (PDF 4); proof p.24 (PDF 26)): "Assuming the
PCP-for-PPAD conjecture, for every fixed rational a ∈ (0, 1) there is a positive rational constant
ε0 = ε0(a) such that computing a normalized additive ε0-equilibrium of an HZ market with utilities in
{0, a, 1} is PPAD-hard."

**Formalization Note** The conjecture is `PCPforPPAD` (weak δ-Pure-Circuit PPAD-hard for some
`δ ∈ (0, 1]`, without the input-once restriction, as the paper quotes [DFHM26, Theorem 2.2] on p.20).
`ε₀` depends only on `a` and is a constant (no `1/N`). PPAD-hardness is the published
`CEPolytopeHard.PPADHard`, the same notion as in the hypothesis. -/
theorem theorem_1_2 (hPCP : PCPforPPAD) (a : ℚ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ ε₀ : ℚ, 0 < ε₀ ∧ CEPolytopeHard.PPADHard (HZConstError a ε₀) := by sorry

end HZTractability.Supplement
